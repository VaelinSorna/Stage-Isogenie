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



# Contexte : Courbe avec anneaux d'endomorphisme

#Exemple de Broker "small"

p = 101 
Fp = GF(p)
E = EllipticCurve(Fp, [79,44])

K.<rK> = QuadraticField(-179)
O = K.maximal_order()                   #Calculer O et K à partir de E ?
dk = K.discriminant()
f = O.conductor()
D = (f^2)*dk

n = 1
Fpn = GF(p^n)
E_eval = EllipticCurve(Fpn, [79,44])
P = E_eval.random_point()

l = 59 #exemple de l'article : l = 31. Exemple avec factorisation non trivial : l = 59


# Etude de la torsion de E

CE = E.cardinality_pari()
tracef = p + 1 - CE
Dm = tracef^2 - 4*p
fm = sqrt(Dm/(dK))

wK = (dK + rK)/2
s = (-fm*dK + tracef)/2   #Un choix parmis deux, s2 = (-fm*dK - tracef)/2
frob = fm*wK + s

Nmax = gcd(s-1,fm/f)

print('cardinal', CE)
print('Torsion', Nmax)