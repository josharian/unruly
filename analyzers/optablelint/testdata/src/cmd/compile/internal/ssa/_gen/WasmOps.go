package main

var ops = []opData{
	{name: "F32x4Pmin"}, // want `F32x4Pmin is commutative, but F32x4Pmin computes pmin\(a, b\) = b < a \? b : a`
	{name: "F32x4Min"},
}
