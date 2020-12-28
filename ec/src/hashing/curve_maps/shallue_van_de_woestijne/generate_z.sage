# Script to generage shallue van de woestijne parameters,
# mildly adapted from the IETF hash to curve draft, section F.1
# https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-09#appendix-F.1

# Enter the following (p, A, B) parameters for your curve, p being the base field order. 
# It is inputted for BLS12-381 by default as an example
p = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
A = 0
B = 4

F = GF(p)

# Arguments:
# - F, a field object, e.g., F = GF(2^521 - 1)
# - A and B, the coefficients of the curve equation y^2 = x^3 + A * x + B
def find_z_svdw(F, A, B, init_ctr=1):
    g = lambda x: F(x)^3 + F(A) * F(x) + F(B)
    h = lambda Z: -(F(3) * Z^2 + F(4) * A) / (F(4) * g(Z))
    # NOTE: if init_ctr=1 fails to find Z, try setting it to F.gen()
    ctr = init_ctr
    while True:
        for Z_cand in (F(ctr), F(-ctr)):
            if g(Z_cand) == F(0):
                # Criterion 1: g(Z) != 0 in F.
                continue
            if h(Z_cand) == F(0):
                # Criterion 2: -(3 * Z^2 + 4 * A) / (4 * g(Z)) != 0 in F.
                continue
            if not h(Z_cand).is_square():
                # Criterion 3: -(3 * Z^2 + 4 * A) / (4 * g(Z)) is square in F.
                continue
            if g(Z_cand).is_square() or g(-Z_cand / F(2)).is_square():
                # Criterion 4: At least one of g(Z) and g(-Z / 2) is square in F.
                return Z_cand
        ctr += 1

print(find_z_svdw(F, A, B))