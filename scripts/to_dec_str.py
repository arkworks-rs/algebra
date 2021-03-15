def from_u64_slice_to_decimal_str(x):
	ret = 0
	for i, limb in enumerate(x):
		print(i)
		print(ret)
		ret += 2 ** (i*64) * limb
	return ret

print(from_u64_slice_to_decimal_str([
    7865245318337523249,
    18346590209729131401,
    15545362854776399464,
    6505881510324251116,
]))
