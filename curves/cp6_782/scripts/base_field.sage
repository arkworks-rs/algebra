modulus = 22369874298875696930346742206501054934775599465297184582183496627646774052458024540232479018147881220178054575403841904557897715222633333372134756426301062487682326574958588001132586331462553235407484089304633076250782629492557320825577

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
