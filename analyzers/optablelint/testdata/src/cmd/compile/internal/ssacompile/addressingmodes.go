package ssacompile

var combine = map[[2]Op]Op{
	{OpAMD64SHRXQload, OpAMD64LEAQ8}: OpAMD64SHRXQloadidx8,
}
