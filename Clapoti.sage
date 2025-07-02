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
#print(frob^2 - tracef*frob + p)
#print(frob2^2 - tracef*frob2 + p)
Nmax = gcd(s-1,fm/f)

frobd = frob
frob2d = frob2
q = p

degmax = 24
torsions = [Nmax]
candidats_KLPT = []
if Nmax^2 > -D:
    facto = Nmax.factor()
    k = len(facto)
    N = 1
    for i in [ 0 .. k-1]:
        N = N*facto[i][0]
    if N^2 > -D:
        candidats_KLPT.append([N,1])
#traces = [tracef]
#cards = [CE]
for d in [2 .. degmax]:
    q = q*p
    frobd = frobd*frob
    frob2d = frob2d*frob2
    tracefd = frobd + frob2d
    Dm = tracefd^2 - 4*q
    fm = int(sqrt(Dm/(dK)))
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
        for i in [ 0 .. k-1]:
            N = N*facto[i][0]
        if N^2 > -D:
            candidats_KLPT.append([N,d])
    #traces.append(tracefd)
    #cards.append(q + 1 - tracefd)

    #print('Test frobs')
    #print(frobd^2 - tracefd*frobd + q)
    #print(frob2d^2 - tracefd*frob2d + q)


print('Torsions', torsions)
print('KLaPoTi', candidats_KLPT)
#print('Traces', traces)
#print('Cards', cards)
#print(E.count_points(degmax))