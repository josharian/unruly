package amd64

func simdV11(s *ssagen.State, v *ssa.Value) *obj.Prog {
	p := s.Prog(v.Op.Asm())
	p.From.Reg = simdReg(v.Args[0])
	p.To.Reg = simdReg(v)
	return p
}

func simdV21(s *ssagen.State, v *ssa.Value) *obj.Prog {
	p := s.Prog(v.Op.Asm())
	p.From.Reg = simdReg(v.Args[1])
	p.AddRestSourceReg(simdReg(v.Args[0]))
	p.To.Reg = simdReg(v)
	return p
}

func simdV11Imm8(s *ssagen.State, v *ssa.Value) *obj.Prog {
	p := s.Prog(v.Op.Asm())
	p.From.Offset = int64(v.AuxUInt8())
	p.AddRestSourceReg(simdReg(v.Args[0]))
	p.To.Reg = simdReg(v)
	return p
}

func simdV21Imm8(s *ssagen.State, v *ssa.Value) *obj.Prog {
	p := simdV21(s, v)
	p.From.Offset = int64(v.AuxUInt8())
	return p
}

func simdV11load(s *ssagen.State, v *ssa.Value) *obj.Prog {
	p := s.Prog(v.Op.Asm())
	p.From.Reg = v.Args[0].Reg()
	ssagen.AddAux(&p.From, v)
	p.To.Reg = simdReg(v)
	return p
}

func simdV2kv(s *ssagen.State, v *ssa.Value) *obj.Prog {
	p := simdV21(s, v)
	p.AddRestSourceReg(maskReg(v.Args[2]))
	return p
}

func simdV2kvResultInArg0(s *ssagen.State, v *ssa.Value) *obj.Prog {
	p := s.Prog(v.Op.Asm())
	p.From.Reg = simdReg(v.Args[1])
	p.AddRestSourceReg(maskReg(v.Args[2]))
	p.To.Reg = simdReg(v)
	return p
}

func simdVkv(s *ssagen.State, v *ssa.Value) *obj.Prog {
	p := s.Prog(v.Op.Asm())
	p.From.Reg = simdReg(v.Args[0])
	p.AddRestSourceReg(maskReg(v.Args[1]))
	p.To.Reg = simdReg(v)
	return p
}

func simdReg(v *ssa.Value) int16 {
	if !v.Type.IsSIMD() {
		base.Fatalf("simdReg: not a simd type; v=%s", v.LongString())
	}
	return simdRegBySize(v.Reg(), v.Type.Size())
}

func maskReg(v *ssa.Value) int16 {
	return v.Reg()
}
