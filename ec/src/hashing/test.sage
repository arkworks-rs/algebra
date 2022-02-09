# Generating test data for the hash to curve module tests
def find_a_0_and_its_ab_non_0_isogenous_of_good_size():
    p = 127
    FF = GF(p)
    for b in range(0,p):
        print(b)
        try:
            E = EllipticCurve([FF(0),FF(b)])
            if E.order() % p == 0:
                print(E)
                iso = find_iso(E)
                if (iso.codomain().order() == 127):
                    print(iso)
                    print("degree, order: ", iso.degree(), iso.codomain().order())
                    print(iso.rational_maps())
                    print("phi_x: ", convert_rational_map_to_str_array(iso.rational_maps()[0]))
                    print("phi_y: ", convert_rational_map_to_str_array(iso.rational_maps()[1]))
                    return iso
                
        except:
            pass

def find_iso(E):
    for p_test in primes(30):
        print("trying isogenies of degree %d"%p_test)
        isos = []
        for i in E.isogenies_prime_degree(p_test):            
            print("checking j-invariant of isogeny ", i)
            jinv = i.codomain().j_invariant()
            print("j-invariant is ", jinv)
            if jinv not in (0, 1728):
                isos.append(i)
                break
        
        if len(isos) > 0:
            print("found isogeny ", isos[0])
            return isos[0].dual()

    return None


def convert_rational_map_to_str_array(the_rational_map):
    rational_map_str = [ [ ], [ ] ]
    rational_map_str[0] = [str(cur_coeff) for cur_coeff in the_rational_map.numerator().coefficients()]
    rational_map_str[1] = [str(cur_coeff) for cur_coeff in the_rational_map.denominator().coefficients()]

    ordered_indcies = len(rational_map_str[0]) < len(rational_map_str[1]) and (0,1) or (1,0)
    for i in range(len(rational_map_str[ordered_indcies[0]]), len(rational_map_str[ordered_indcies[1]])):
        rational_map_str[ordered_indcies[0]].insert(0,'0')
    
    return rational_map_str

