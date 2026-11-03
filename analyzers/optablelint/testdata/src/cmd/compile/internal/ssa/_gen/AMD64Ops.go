// Op definitions for the synthetic tables in optablelint_test.go.
// Only the names and line numbers matter.

package main

var ops = []opData{
	{name: "MOVQloadidx8"},
	{name: "SHRXQloadidx8"},          // want `SHRXQloadidx8 is faultOnNilArg0, but it is indexed: it addresses arg0\+8\*arg1\+off.*\(no rule produces it; ssacompile/addressingmodes.go refers to it\)`
	{name: "ADDLloadidx4"},           // want `ADDLloadidx4 is faultOnNilArg1, but it is indexed: it addresses arg1\+4\*arg2\+off.*\(latent: nothing produces it\)`
	{name: "LoweredMemEq"},           // want `LoweredMemEq is faultOnNilArg0 and faultOnNilArg1, but it is a call, and the callee need not dereference`
	{name: "VMOVDQU32Masked512load"}, // want `VMOVDQU32Masked512load is faultOnNilArg0, but its memory access is masked`
	{name: "KMOVQstore"},
	{name: "VMINPD128"}, // want `VMINPD128 is commutative, but VMINPD returns its second operand if either is NaN`
	{name: "VPMINSD128"},
}
