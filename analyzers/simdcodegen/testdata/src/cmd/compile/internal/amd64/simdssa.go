package amd64

func ssaGenSIMDValue(s *ssagen.State, v *ssa.Value) bool {
	var p *obj.Prog
	switch v.Op {
	case ssaop.OpAMD64VPSLLD512const:
		p = simdV11Imm8(s, v)
	case ssaop.OpAMD64VPSLLDMasked512constMerging,
		ssaop.OpAMD64VPADDDMasked512Merging:
		p = simdV2kvResultInArg0(s, v)
	case ssaop.OpAMD64VPADDD512:
		p = simdV21Imm8(s, v)
	case ssaop.OpAMD64VPSHUFD512load:
		p = simdV11load(s, v)
	case ssaop.OpAMD64VPSUBD512:
		p = simdV11(s, v)
	case ssaop.OpAMD64VPABSD512:
		p = simdV21(s, v)
	case ssaop.OpAMD64VPADDDMasked512,
		ssaop.OpAMD64VPBLENDMDMasked512:
		p = simdV2kv(s, v)
	case ssaop.OpAMD64VPABSDMasked512:
		p = simdVkv(s, v)
	case ssaop.OpAMD64VPEXTRD128:
		// Inline codegen, as in wasm/simdssa.go.
		p = s.Prog(v.Op.Asm())
		p.From.Offset = v.AuxInt
		p.From.Reg = simdReg(v.Args[0])
	default:
		return false
	}

	switch v.Op {
	case ssaop.OpAMD64VPABSDMasked512,
		ssaop.OpAMD64VPADDDMasked512Merging:
		x86.ParseSuffix(p, "Z")
	}
	return true
}
