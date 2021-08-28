def generate_from_bytes_mod_order_test_vector(modulus):
    def gen_vector(number):
        byte_arr = convert_int_to_byte_vec(number)
        # s = str(number % modulus)
        # return "(" + byte_arr + ", \"" + s + "\"),"
        return byte_arr + ","

    data = ["vec!["]

    small_values_to_test = [0, 1, 255, 256, 256 * 256 + 255]
    modulus_bits = int((len(bin(modulus)[2:]) + 7) / 8) * 8
    values_to_test = small_values_to_test + [
        modulus >> 8,
        (modulus >> 8) + 1,
        modulus - 1,
        modulus,
        modulus + 1,
        modulus * 2,
        modulus * 256,
        17 + (1 << modulus_bits),
        19 + (1 << modulus_bits) + modulus,
        81 + (1 << modulus_bits) * 256 + modulus,
    ]

    for i in values_to_test:
        data += ["// " + str(i)]
        data += [gen_vector(i)]

    data += ["];"]
    return "\n".join(data)


def convert_int_to_byte_vec(number):
    s = bin(number)[2:]
    num_bytes = int((len(s) + 7) / 8)
    s = s.zfill(num_bytes * 8)

    byte_arr = []
    for i in range(num_bytes):
        byte = s[i * 8 : (i + 1) * 8]
        i = int(byte, 2)
        byte_arr += [str(i) + "u8"]

    data = ", ".join(byte_arr)
    return "vec![" + data + "]"


bls12_fr_mod = (
    52435875175126190479447740508185965837690552500527637822603658699938581184513
)
print(generate_from_bytes_mod_order_test_vector(bls12_fr_mod))
