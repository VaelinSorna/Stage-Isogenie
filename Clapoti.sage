from sage.rings.finite_rings.integer_mod import square_root_mod_prime
from sage.rings.finite_rings.integer_mod import square_root_mod_prime_power
from sage.rings.number_field.order_ideal import NumberFieldOrderIdeal
from sage.schemes.elliptic_curves.hom_velusqrt import EllipticCurveHom_velusqrt
from sage.schemes.elliptic_curves.weierstrass_morphism import *
from sage.groups.generic import order_from_multiple
from sage.schemes.elliptic_curves.ell_curve_isogeny import compute_isogeny_bmss
from sage.schemes.elliptic_curves.hom_frobenius import EllipticCurveHom_frobenius
from sage.libs.libecm import ecmfactor
from sage.misc.search import search
import time
from myklpt2 import klpt



# CONTEXTE : Courbe avec anneaux d'endomorphisme

#Exemple de Broker "small"

p = 101
Fp = GF(p)
E = EllipticCurve(Fp, [79,44])

K.<rK> = QuadraticField(-179)
O = K.maximal_order()                   #Calculer O et K à partir de E ?
dK = K.discriminant()
f = O.conductor()
D = (f^2)*dK

n = 24
Fpn = GF(p^n)
E_eval = EllipticCurve(Fpn, [79,44])
P = E_eval.random_point()

l = 59 #exemple de l'article : l = 31. Exemple avec factorisation non trivial : l = 59




# ETUDE DE LA TORSION DE E

CE = E.cardinality_pari()
tracef = p + 1 - CE
Dm = tracef^2 - 4*p
fm = int(sqrt(Dm/(dK)))

wK = (dK + rK)/2
s = int((-fm*dK + tracef)/2)
s2 = (-fm*dK - tracef)/2
frob = fm*wK + s
frob2 = -(fm*wK + s2)
assert (frob^2 - tracef*frob + p) == 0
assert (frob2^2 - tracef*frob2 + p) == 0

if dK%4 == 1 :
    a = int((tracef - fm)/2)
else :
    a = int(tracef/2)
Nmax = gcd(a-1,fm/f)
torsions = [Nmax]

candidats_KLPT = []
if Nmax^2 > -D:
    facto = Nmax.factor()
    k = len(facto)
    factoN = []
    N = 1
    for i in [ 0 .. k-1]:
        N = N*facto[i][0]
        factoN.append(facto[i][0])
    if N^2 > -D:
        candidats_KLPT.append([N,factoN,1])

#traces = [tracef]
#cards = [CE]
frobd = frob
frob2d = frob2
q = p
degmax = 24
for d in [2 .. degmax]:
    q = q*p
    frobd = frobd*frob
    frob2d = frob2d*frob2
    tracefd = frobd + frob2d
    Dm = tracefd^2 - 4*q
    fm = int(sqrt(Dm/(dK)))
    assert (frobd^2 - tracefd*frobd + q) == 0
    assert (frob2d^2 - tracefd*frob2d + q) == 0
    if dK%4 == 1 :
        a = int((tracefd - fm)/2)
    else :
        a = int(tracefd/2)
    Nd = gcd(a-1,fm/f)
    torsions.append(Nd)
    if Nd^2 > -D:
        facto = Nd.factor()
        k = len(facto)
        N = 1
        factoN = []
        for i in [ 0 .. k-1]:
            N = N*facto[i][0]
            factoN.append(facto[i][0])
        if N^2 > -D:
            candidats_KLPT.append([N,factoN,d])
    #traces.append(tracefd)
    #cards.append(q + 1 - tracefd)



print('Torsions', torsions)
print('Candidats KLaPoTi', candidats_KLPT)
#print('Traces', traces)
#print('Cards', cards)
#print(E.count_points(degmax))






# TEST SOLUTIONS KLPT



def ideal_de_norme(l,f,D):

    #Trouver un idéal de norme l premier : Cf notes de cours Biasse
    #On se place dans un ordre de discriminant D et de conducteur f
    
    if kronecker(D,l) == 1:
        D = Mod(D,l)
        sq = square_root_mod_prime(D,l) #Lien avec Seysen ? Prendre le min des deux racines vu dans N ? (Optionnel)
        sm = Mod(-sq,l)
        sq = ZZ(sq)
        sm = ZZ(sm)
        sq = min(sm,sq)
        #print(sq)
        return NumberFieldOrderIdeal(O,[l, -sq + f*t]) #Forme donnée dans le cours de Biasse
    elif kronecker(D,l) == 0:
        return NumberFieldOrderIdeal(O,[l, f*t])
    else:
        raise "l est inerte"





def sol_KLPT(N,factoN,aa):

    #Utiliser KLPT pour résoudre l'equation définie par N et aa

    l, α = aa.gens_two()
    Quat.<i,j,k> = QuaternionAlgebra(-1, dK)
    assert (α[0] + α[1]*j).reduced_norm() == α.norm()
    assert (α[0] + α[1]*j).reduced_trace() == α.trace()
    assert j.reduced_norm() == rK.norm() and j.reduced_trace() == rK.trace()
    r = α.parent().number_field().gen()
    assert (r+1)/2 in self.ctx.O   #Necessaire ? ordre de discriminant = 1 mod 4 ?
    OO = Quat.quaternion_order([1, i, (1+j)/2, (i+k)/2])
    I = OO*N + OO*(α[0] + α[1]*j)
    print(f'{I = }')


    elt = klpt(I,N,factoN)
    assert elt in I
    print(f'{elt = }', '| norm:', elt.reduced_norm().factor())
    

    b = elt[0] + elt[2]*r
    c = elt[1] + elt[3]*r
    while b and c and b/2 in aa and c/2 in aa:  # can we avoid this a priori in KLPT?
        b /= 2
        c /= 2
    print(f'{b = }')
    print(f'{c = }')
    assert b in aa
    assert c in aa
    bb = O.ideal([g*b.conjugate()/aa.norm() for g in aa.gens()])
    cc = O.ideal([g*c.conjugate()/aa.norm() for g in aa.gens()])
    print(f'{bb = }', bb.norm())#.factor())
    print(f'{cc = }', cc.norm())#.factor())
    assert ZZ(bb.norm() + cc.norm()).prime_divisors() == [2]
    if bb.norm().gcd(cc.norm()) != 1:
        print('solution premier entre eux')
        return bb.norm(), cc.norm(), False
    else :
        print('mauvaise solution !')
        return bb.norm(), cc.norm(), True
        
        
        


aa = ideal_de_norme(l,f,D)
k_candidats = len(candidats_KLPT)
for i in [ 0 .. k_candidats - 1]:
    N = candidats_KLPT[i][0]
    factoN = candidats_KLPT[i][1]
    Nb, Nc, verif = sol_KLPT(N,factoN,aa)
    

