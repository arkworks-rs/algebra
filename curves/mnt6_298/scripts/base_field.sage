modulus = 475922286169261325753349249653048451545124878552823515553267735739164647307408490559963137

assert(modulus.is_prime())

Fp = GF(modulus)

generator = Fp(0);
for i in range(0, 20):
    i = Fp(i);
    neg_i = Fp(-i)
    if not(i.is_primitive_root() or neg_i.is_primitive_root()):
        continue
    elif i.is_primitive_root():
        assert(i.is_primitive_root());
        print("Generator: %d" % i)
        generator = i
        break
    else:
        assert(neg_i.is_primitive_root());
        print("Generator: %d" % neg_i)
        generator = neg_i
        break


two_adicity = valuation(modulus - 1, 2);
trace = (modulus - 1) / 2**two_adicity;
two_adic_root_of_unity = generator^trace
print("2-adic Root of Unity: %d " % two_adic_root_of_unity)
