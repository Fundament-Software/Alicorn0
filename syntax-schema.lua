local schema = require "schema"

local S = schema.create(
	"alicorn0_syntax",
	"the raw format that an alicorn zero source text should be parsed into",
	"b2771894692e6ccdbb737b163d45ea90"
)

S:struct "anchor" "The source position information attached to a node" {
	schema.text "sourceid"(0) "the file name or other identifying information to locate and distinguish the original source of the code", --TODO: consider making this a generic parameter to accept structured data.
	schema.u32 "line"(1) "the line number in the file",
	schema.u32 "char"(2) "the offset within the line",
}

S:struct "symbol" "A string from the source" {
	schema.text "str"(0) "the string",
	S.export.anchor "start_anchor"(1),
	S.export.anchor "end_anchor"(2),
}

local element = S:addstruct("element")

element:define {
	S.export.anchor "start_anchor"(0) "the source location of the element",
	schema.union "kind"(1) "What syntactic element this represents" {
		schema.variant "list"(2) {
			schema.list(element) "elements"(3),
			S.export.anchor "end_anchor"(4),
		},
		schema.variant "string"(5) {
			schema.list(element) "elements"(6) "A string contains a list of elements corresponding to parts of the literal. Every splice becomes a separate element, and the region between them is a literal byte buffer element",
			S.export.anchor "end_anchor"(7),
		},
		schema.variant "literal"(8) {
			schema.union "literaltype"(9) {
				schema.variant "u8"(10) {
					schema.u8 "val"(11),
				},
				schema.variant "i8"(12) {
					schema.i8 "val"(13),
				},
				schema.variant "u16"(14) {
					schema.u16 "val"(15),
				},
				schema.variant "i16"(16) {
					schema.i16 "val"(17),
				},
				schema.variant "u32"(18) {
					schema.u32 "val"(19),
				},
				schema.variant "i32"(20) {
					schema.i32 "val"(21),
				},
				schema.variant "u64"(22) {
					schema.u64 "val"(23),
				},
				schema.variant "i64"(24) {
					schema.i64 "val"(25),
				},
				schema.variant "f16"(26) {
					schema.f16 "val"(27),
				},
				schema.variant "f32"(28) {
					schema.f32 "val"(29),
				},
				schema.variant "f64"(30) {
					schema.f64 "val"(31),
				},
				schema.variant "bytes"(32) {
					schema.list(schema.u8) "val"(33),
				},
				schema.variant "unit"(34) {},
			},
		},
	},
}

return S
