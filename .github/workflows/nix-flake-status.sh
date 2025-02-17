#!/usr/bin/env bash
set -euo pipefail

# Configuration
NIX_FILE="${1:-status.nix}"
DRY=
GITHUB_TOKEN="${GITHUB_TOKEN:-}"

if [[ -z "${GITHUB_TOKEN}" ]]; then
    GITHUB_TOKEN="$(gh auth token)"
fi

GITHUB_REPO="${GITHUB_REPO:-Fundament-Software/Alicorn0}"
COMMIT_SHA="${COMMIT_SHA:-$(git rev-parse HEAD)}"
CHECK_SUITE_ID=""
USE_CHECKS="${GITHUB_RUN_ID:+true}"  # should imply we can use check suites

# Check for local changes or if we're ahead of remote
if [[ -n "$(git status --porcelain)" ]] || [[ -n "$(git log @{u}.. 2>/dev/null)" ]]; then
    echo "Local changes or commits ahead of remote detected - running in dry-run mode"
    DRY=echo
fi

# Function to create a check suite
create_check_suite() {
    local response
    response=$($DRY curl -s -X POST \
        -H "Authorization: token ${GITHUB_TOKEN}" \
        -H "Accept: application/vnd.github.v3+json" \
        "https://api.github.com/repos/${GITHUB_REPO}/check-suites" \
        -d "{
            \"head_sha\": \"${COMMIT_SHA}\"
        }")
    CHECK_SUITE_ID=$(echo "$response" | jq -r '.id')
    echo "Created check suite: $CHECK_SUITE_ID"
}

# Function to create a check run within the suite
create_check_run() {
    local name="$1"
    local status="$2"
    local conclusion="$3"
    local details="$4"
    
    $DRY curl -s -X POST \
        -H "Authorization: token ${GITHUB_TOKEN}" \
        -H "Accept: application/vnd.github.v3+json" \
        "https://api.github.com/repos/${GITHUB_REPO}/check-runs" \
        -d "{
            \"name\": \"${name}\",
            \"head_sha\": \"${COMMIT_SHA}\",
            \"status\": \"${status}\",
            \"check_suite_id\": \"${CHECK_SUITE_ID}\",
            \"conclusion\": \"${conclusion}\",
            \"output\": {
                \"title\": \"${name}\",
                \"summary\": \"${details}\"
            }
        }"
}

# Function to post status using the Status API
post_status() {
    local state="$1"
    local description="$2"
    local context="$3"
    
    $DRY curl -s -X POST \
        -H "Authorization: token ${GITHUB_TOKEN}" \
        -H "Accept: application/vnd.github.v3+json" \
        "https://api.github.com/repos/${GITHUB_REPO}/statuses/${COMMIT_SHA}" \
        -d "{
            \"state\": \"${state}\",
            \"description\": \"${description}\",
            \"context\": \"${context}\"
        }"
}

# Function to update build status (uses either Checks or Status API)
update_status() {
    local state="$1"
    local description="$2"
    local context="$3"
    
    if [ "${USE_CHECKS}" = "true" ]; then
        # Map status states to check states/conclusions
        local check_status="completed"
        local conclusion
        case "$state" in
            "pending") 
                check_status="in_progress"
                conclusion="neutral"
                ;;
            "success") conclusion="success" ;;
            "failure") conclusion="failure" ;;
            *) conclusion="neutral" ;;
        esac
        
        create_check_run "$context" "$check_status" "$conclusion" "$description"
    else
        post_status "$state" "$description" "$context"
    fi
}

# Checks if an attribute was built successfully - doesn't actually do the building
build_result_to_status() {
    local attr="$1"
    local path="$2"
    
    echo "Checking if ${attr} was built at ${path}..."

    if [ -e "$path" ] && nix-store --verify-path "$path"; then
        update_status "success" "Successfully built ${attr} at ${path}" ".#${attr}"
        return 0
    else
        update_status "failure" "Failed to build ${attr} at ${path}" ".#${attr}"
        return 1
    fi
}

# Get all attributes from the Nix file
get_attrs() {
    nix-instantiate --eval --json \
        -E "builtins.attrNames (import ./${NIX_FILE} {})" \
        | jq -r '.[]'
}

get_drvs() {
    nix-env -f "./${NIX_FILE}" -qaP --json --drv-path --out-path --show-trace | jq -r '.[].drvPath'
}

main() {
    local failed=0

    # Only create check suite if we're using checks
    if [ "${USE_CHECKS}" = "true" ]; then
        create_check_suite
    fi

    update_status "pending" "Evaluating Nix expressions" "eval"

    # Get all attributes
    echo "Evaluating ${NIX_FILE} for attributes..."
    attrs=$(get_attrs)
    
    if [ -z "$attrs" ]; then
        update_status "failure" "eval error or no derivations" "eval"
        echo "No attributes found in ${NIX_FILE}"
        exit 1
    fi
    
    update_status "pending" "Starting builds" "build"
    update_status "success" "Evaluation succeeded" "eval"

    echo "Getting attr to output paths"
    inf=$(nix-env -f "./${NIX_FILE}" -qaP --json --drv-path --out-path --show-trace)
    echo "Getting drv paths"
    drvs=$(echo "$inf" | jq -r '.[].drvPath')

    echo "Instantiating drvs"
    nix-instantiate --strict --json -E "import ./${NIX_FILE} {}" >&2

    # Builds everything (in parallel)
    nix-build -j 4 --no-link $drvs --keep-going --log-format bar >&2 || true

    update_status "success" "built" "build"
    
    # Check if each attribute was built successfully
    echo "$inf" | jq -r 'to_entries | .[] | "\(.key) \(.value.outputs.out)"' | while read -r key attr; do
        echo "key: $key, attr: $attr"
        if ! build_result_to_status "${key}" "${attr}"; then
            failed=$((failed + 1))
        fi
    done
    
    # Exit with failure if any builds failed
    [ "$failed" -eq 0 ] || exit 1
}

main

