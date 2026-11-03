// Op definitions for the synthetic tables in simdcodegen_test.go.
// Only the names and line numbers matter.

package main

var ops = []opData{
	{name: "VPSLLD512const"},
	{name: "VPSLLDMasked512constMerging"}, // want `VPSLLDMasked512constMerging has aux UInt8, but its codegen at simdssa.go:\d+ \(simdV2kvResultInArg0\) never reads v.AuxInt or v.Aux: the immediate is dropped`
	{name: "VPADDD512"},                   // want `VPADDD512 has no aux, but its codegen at simdssa.go:\d+ \(simdV21Imm8\) reads it`
	{name: "VPSHUFD512load"},              // want `VPSHUFD512load has aux SymValAndOff, but its codegen .* does not decode it with AuxValAndOff`
	{name: "VPSUBD512"},                   // want `VPSUBD512 takes arg1 in a register, but its codegen at simdssa.go:\d+ \(simdV11\) never reads v.Args\[1\]`
	{name: "VPABSD512"},                   // want `VPABSD512 has 1 args, but its codegen at simdssa.go:\d+ \(simdV21\) reads v.Args\[1\]: the compiler panics`
	{name: "VPADDDMasked512"},             // want `VPADDDMasked512 is masked, but its codegen .* does not emit zeroing-masking`
	{name: "VPADDDMasked512Merging"},      // want `VPADDDMasked512Merging is a merging op, but it is emitted with zeroing-masking`
	{name: "VPBLENDMDMasked512"},
	{name: "VPABSDMasked512"},
	{name: "VPEXTRD128"},
	{name: "VPMISSING512"}, // want `VPMISSING512 has no codegen`
}
