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

def ideal_de_norme(l,f,D):

    #Trouver un idéal de norme l premier : Cf notes de cours Biasse
    #On se place dans un ordre de discriminant D et de conducteur f.
    
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

#La racine utilisée ici n'est pas le coefficient b de la forme quadratique associée.




def forme_de_norme(l,D):

    #Calcule une forme quadratique binaire primitive normale de coefficient dominant l, de discriminant D. 
    #On demande à ce que l soit décomposé dans l'ordre de discriminant D.
    
    if kronecker(D,l) == 1:
        if l == 2 :
            d = Mod(D,8)
            b = square_root_mod_prime_power(d,2,3)
            b = ZZ(b)
        else :
            x = Mod(D,4)
            d = Mod(D,l)
            y = square_root_mod_prime(d,l)
            b = x.crt(y)
            b = ZZ(b)
        ql = BinaryQF([l,b, int(int((b^2 - D))/int(4*l))])
        return ql
    else:
        raise ValueError('l pas split')


def base_fwk(b,dk,f):
    
    #Dans K = Q(rk) quadratique de discriminant dk, on se donne b = x + y*rk dans un ordre O
    #On veut écrire b dans la base [1,f*wk] de l'ordre O, wk = (dk + rk)/2.
    
    x = b[0]
    y = b[1]
    xw = x - dk*y
    yw = (2*y)/f   #xw, yw sont dans ZZ. 
    return xw,yw
    
def base_fq1(b,fm,dk,f,tracef):
    
    # On représente le froebenius fq par le complexe (tracef + fm*rk)/2 dans K = Q(rk).
    # Remarque : il est a priori possible que fq soit représenté par (tracef - fm*rk)/2 .

    # On écrit b = (xf + yf*fq)/fm, et on calcule xf, yf dans ZZ.
    
    # Il existe s1 entier tel que fq = fm*wk + s1.
    
    
    s1 = (-fm*dk + tracef)/2
    (x,y) = base_fwk(b,dk,f)
    xf = fm*x - y*s1*f
    yf = y*f
    return xf,yf


def eval_fq(P,kq,E):

    #calcul Frobenius_q(P) sur une courbe E définie sur Fq, avec q = p^(kq) et p premier.
    #On suppose que P appartient à E(Fq).
    
    if P == E(0):
        return P
    else :
        frob = EllipticCurveHom_frobenius(E, kq)
        return frob(P)

def formes_generatrices (D,N,test_norm): #Trouver la borne : Analyse de Jao

# Trouver une famille génératrice du groupes de classes, vu comme formes quadratiques réduites.
# En n'utilisant que des idéaux de normes premiers autorisés pour le calcul d'isogénies horizontales.
# On génère simplement une famille de N idéaux, N supposé suffisament grand pour que leurs classes soient génératrices.
# N = 2log^2(D) suffit (Admet hypothèse de Riemann Généralisée).
    
    Idéaux = []
    Formes = []
    Primes = []
    i = 2
    while i < N:
        if kronecker(D,i) == 1 and (test_norm)%i != 0:
            Primes.append(i)
            qi = forme_de_norme(i,D)
            Li = NumberFieldOrderIdeal(O,qi)
            Idéaux.append(Li)
            Formes.append(qi)
        i = next_prime(i)
    return Idéaux, Formes, Primes



def factor_ecm(a,Primes):  

    #On utilise ECM pour vérifier que l'entier a se factorise uniquement avec les nombres premiers de la liste Primes. 
    #Si a est friable, on calcule sa décomposition en facteurs premiers.
    
    produit = a
    facteur = 1
    reste = a
    
    factorisation = []
    friable = True         # Dès que l'on trouve un facteur qui contredit la friabilité, on s'arrête. 
    count = 0              # On évite les boucles infinies. 

    while produit > 1 and friable:
        
        assert count < 1000
        
        # On teste si produit est un nombre premier.

        if produit.is_prime() :
            facteur = produit
            reste = 1 
         

        else:
            testecm = ecmfactor(produit, 0.00)
            #testecm[0] == False ssi pas de facteur trouvé. testecm[1] == produit ssi le facteur trouvé est trivial maximal.
            while (testecm[0] == False or testecm[1] == produit):
                if count < 1000:
                    testecm = ecmfactor(produit, 0.00)
                    count = count + 1
                else:
                    print('WARNING ECM ne trouve pas de facteur pour :', produit)  #Peut arriver sur de petits nombres, tester ecmfactor(9,0.00)
                    facto_brut = produit.factor()
                    testecm = (True, facto_brut[0][0], 0)
                    count = 0
            facteur = testecm[1]
            reste = produit//facteur

        # On vérifie que le facteur trouvé est premier, sinon on le factorise encore
        
        while facteur.is_prime() == False:
            if count < 1000:
                testecm2 = ecmfactor(facteur, 0.00)
                count = count + 1
            else:
                print('WARNING ECM facto_brut pour factoriser :', facteur)
                facto_brut = produit.factor()
                testecm2 = (True, facto_brut[0][0], 0)
                count = 0
            if testecm2[0] == True :
                facteur2 = testecm2[1]
                reste = reste*(facteur//facteur2)
                facteur = facteur2
    

        # On teste le facteur premier trouvé. Si il est dans Primes, on calcule sa valuation. 
        
        if search(Primes,facteur)[0]: #search est un algorithme de recherche dans une liste triée.
            exposant = 1
            while reste%facteur == 0:
                exposant = exposant + 1
                reste = reste//facteur
            factorisation.append([facteur, exposant])
        else:
            factorisation.append([facteur, 1])
            factorisation.append([reste, 1])
            friable = False
            
        produit = reste 
        
    return friable, factorisation


# Version 1: Algorithme énoncé par Jao Soukarev. 

def factorisation(L,D,N,Borne_z,test_norm):

    #On suppose L être un idéal de norme l premier décomposé.
    #On cherche à ramener la classe de L à une classe simplifiable en multipliant au hasard par des petits idéaux.
    #On représente les classes par des formes quadratiques réduites, et on cherche un formes de coefficients dominant friable.
    
    #Implémentation de l'algorithme énoncé par Jao et Soukharev.
    #Borne_z est une borne donnée par Jao dans l'analyse de l'algorithme. Le nombres de produits aléatoires ne dépassera pas Borne_z. 
    
    Idéaux, Formes, Primes = formes_generatrices(D,N,test_norm)
    k = len(Primes)
    
    ql = (L.quadratic_form()).reduced_form() #Représente la classe de L
    a = ql[0]
    relation = ql        # Partant de ql, on va chercher une classe simplifiable
    
    expx = [0]*k  # La liste des exposants donnants des produits aléatoires effectués
    liste_indice = []
    compte = 0
    test_facto, facto = factor_ecm(a,Primes)
    
    while test_facto == False:
        compte = compte + 1  
        assert compte < 1000  #sécurité arbitraire
        
        # Choix d'exposants au hasard, on veut entre 3 et Borne_z coefficients non nuls (Cf algo 3 Jao Soukharev)
        
        expx = [0]*k  # La liste des exposants donnants des produits aléatoires effectués
        nb_indice = randint(3,Borne_z) 
        
        liste_indice = []   # On choisit les idéaux qui vont intervenir dans la factorisation, au hasard.
        while len(liste_indice) < min(nb_indice,k):
            i = randint(0,k-1)
            if i not in liste_indice :
                liste_indice.append(i)
        
        for i in liste_indice:
            expi = randint(1,int((N/Primes[i])^2))   #On attribue à chaque indice un exposant xi, bornée d'après Jao Soukharev.
            expx[i] = expi

        # Calcul de ql*( fi^exp(xi) pour tout i ) 
        
        relation = ql
        for i in [0 .. k-1]:
            for _ in [1 .. (expx[i])]:
                relation = (relation*Formes[i]).reduced_form()
                
        a = relation[0] 
        test_facto, facto = factor_ecm(a,Primes)
         
    
    #Simplification de la classe "relation" trouvée

    expu = [0]*k     #liste des exposants de l'écriture de "relation" dans la famille génératrice
    ka = len(facto)
    b = relation[1]
    for j in [0 .. ka-1]:
        i = 0
        while Primes[i] != facto[j][0]:
            i = i+1
        expu[i] = facto[j][1]
        bi = Formes[i][1]
        if Mod( b , 2*Primes[i]) != Mod( bi , 2*Primes[i]):
                    expu[i] = -expu[i]
        
    
    #Inverser la relation pour trouver L:
    
    expe = []     #liste des exposants de l'écritures de L dans la famille génératrice, positifs.
    factoL = []    #Idéaux apparaissant dans l'écriture de L dans la famille génératrice.
    for i in [0 .. k-1] :
        ei = expu[i] - expx[i]
        if ei > 0 :
            expe.append(ei)
            factoL.append(Idéaux[i])
        elif ei < 0 :
            expe.append(-ei)
            factoL.append(Idéaux[i].conjugate())
            
    
    return expe, factoL, #compte



# Version 2: avec une borne de pas de marche aléatoire dans un graphe expanseur.

def factorisation_2(L,D,N,Borne_t,test_norm):
    
    ##On suppose L être un idéal de norme l premier décomposé.
    #On cherche à ramener la classe de L à une classe simplifiable en multipliant au hasard par des petits idéaux.
    #On représente les classes par des formes quadratiques réduites, et on cherche un formes de coefficients dominant friable.
    
    #Borne_t est le nombre de pas nécessaire pour obtenir des marches aléatoires uniformes dans le groupe de classes d'idéaux.
    
    Idéaux, Formes, Primes = formes_generatrices (D,N,test_norm)
    k = len(Primes)
    
    ql = (L.quadratic_form()).reduced_form() #Représente la classe de L.
    a = ql[0]
    relation = ql        # Partant de ql, on va chercher une classe simplifiable.
    
    expx = [0]*k         # La liste des exposants donnants des produits aléatoires effectués.
    compte = 0
    test_facto, facto = factor_ecm(a,Primes)
    
    while test_facto == False:
        compte = compte + 1
        assert compte < 1000  #sécurité arbitraire
        
        #On effectue une marche aléatoire en partant de ql, de Borne_t pas. 
        
        expx = [0]*k   # La liste des exposants donnants des produits aléatoires effectués.
        for i in [1 .. Borne_t]:
            indice = randint(0,k-1)
            increment = randint(0,1)
            if increment == 0:
                increment = -1
            expx[indice] = expx[indice] + increment
            
            
        # Calcul de ql*( fi^exp(xi) pour tout i ) 
        
        relation = ql
        for i in [0 .. k-1]:
            facteur = Formes[i]
            exp = expx[i]
            if exp < 0:
                facteur = BinaryQF([facteur[0],-facteur[1],facteur[2]])
                exp = -exp
            for _ in [1 .. exp]:
                relation = (relation*facteur).reduced_form()   #Toujours réduire : bonne idée ??
        a = relation[0] #Si a factorise complétement dans Primes, c'est gagné avec Seysen
        test_facto, facto = factor_ecm(a,Primes)
    
    #Simplification de la classe "relation" trouvée:

    expu = [0]*k          #liste des exposants de l'écriture de "relation" dans la famille génératrice
    ka = len(facto)
    b = relation[1]
    for j in [0 .. ka-1]:
        i = 0
        while Primes[i] != facto[j][0]:
            i = i+1
        expu[i] = facto[j][1]
        bi = Formes[i][1]
        if Mod( b , 2*Primes[i]) != Mod( bi , 2*Primes[i]):
                    expu[i] = -expu[i]
        
    
    #Inverser la relation pour trouver L:
    
    expe = []     #liste des exposants de l'écritures de L dans la famille génératrice, positifs.
    factoL = []    #Idéaux apparaissant dans l'écriture de L dans la famille génératrice.
    for i in [0 .. k-1] :
        ei = expu[i] - expx[i]
        if ei > 0 :
            expe.append(ei)
            factoL.append(Idéaux[i])
        elif ei < 0 :
            expe.append(-ei)
            factoL.append(Idéaux[i].conjugate())
            
    
    return expe, factoL #,compte

def coeff_courbe_l_isogene(E,l,h,Psi_l):

    #Formules donnant un modèle rationel de la courbe image de la l-isogénie partant de E, de j-invariant h
    #Le polynôme modulaire Psi_l est précalculé. 
    
    F = E.base_field()
    j = E.j_invariant()
    a = E.a4()
    b = E.a6()
    
    ZXY = Psi_l.parent()
    (X,Y) = ZXY.gens()
    PsiX = (Psi_l.derivative(X))
    PsiX_eval = PsiX(j,h)
    PsiY = (Psi_l.derivative(Y))
    PsiY_eval = PsiY(j,h)
    assert PsiY_eval != 0
    
    h1 = F(-18/l)*(b/a)*(PsiX_eval/PsiY_eval)*j
    A = F(-1/48)*(h1^2)/((h-1728)*h)
    B = F(-1/864)*(h1^3)/((h-1728)*h^2)
    A = A*(F(l)^4) #Normalisation
    B = B*(F(l)^6)
    return A,B


def CheckElkies(E, ell, kernel_polynomial, lam):   #Implémentation de Pegasis, prise dans le fichier Elkies.py.
    r"""Given a kernel polynomial, verify it corresponds to the correct eigenvalue

    If the multiplication-by-lambda map has the following standard form in
    rational maps (c.f. Sutherland's lectures)

        [\lambda] = (u(x)/v(x), r(x, y)/s(x))

    then the eigenvalue is correct, if

        \pi(P) = \lambda P

    on all points in the kernel of the isogeny defined by kernel_polynomial.

    Note that r(x, y) = r(x, 1) * y, by the standard form of isogenies. So, if
    P = (x, y), this is equivalent to

        (x^p, y^p) = (u(x)/v(x), r(x, 1)/s(x) * y)

    for points in ker(\varphi)

    Verifying the first component is easy. To verify the second, we note that

            y^p = r(x, 1)/s(x) * y
        <=> y^{p-1} = r(x, 1)/s(x)
        <=> f(x)^{(p-1)/2} = r(x, 1)/s(x)
        <=> f(x)^{(p-1)/2} * s(x) = r(x, 1)

    where f(x) is the defining equation of the curve E: y^2 = f(x).
    """

    p = E.base_field().characteristic()
    E = E.short_weierstrass_model()

    # Defining equation of E: y^2 + g(x)y = f(x)
    f, g = E.hyperelliptic_polynomials()

    # Must be true, because E is in Weierstrass form
    assert g == 0

    # For efficiency: replace lambda with -lambda if -lambda has smaller
    # absolute value
    # If we switch, then we need to multiply the isogeny with -1
    # (which is multiplication by -1 on the y-coordinate)

    if lam > ell - lam:
        lam = ell - lam
        sign = -1
    else:
        sign = 1

    if lam == 1:
        Y = pow(f, (p - 1) / 2, kernel_polynomial)
        return sign * Y == 1

    # Build extension over which the x-coordinates of the kernel are defined
    extension = kernel_polynomial.parent().quotient_ring(kernel_polynomial)

    # Get rational functions of multiplication-by-lambda
    # x = u/v, y = r/x as in the description in the docstring
    x, y = E.multiplication_by_m(lam)[:2]
    u = extension(x.numerator())
    v = extension(x.denominator())
    # Overwrite r(x, y) with r(x, 1)
    r = y.numerator()
    r = extension(r(r.variables()[0], 1).univariate_polynomial())
    s = extension(y.denominator())

    # x^p in the extension
    Xp = extension(pow(kernel_polynomial.parent().gens()[0], p, kernel_polynomial))

    # Verify u(x)/v(x) = x^p
    if u != Xp * v:
        return False

    Y = extension(pow(f, (p - 1) / 2, kernel_polynomial))

    # Verify y^{p-1} = f(x)^{(p-1)/2} = sign * r(x, 1)/s(x)
    return Y * s == sign * r



def polynome_ker(E,l,L,f,fm,dk,tracef,j,j_prec,Psi_l):

    #Calcul du polynôme décrivant le noyau de la l-isogénie définie par l'action de L sur E. 
    #Si on enchaine les calculs pour un même idéal L, j_prec est le j_invariants du dépard précédent. 
    #On suppose le polynôme modulaire Psi_l précalculé. 

    assert gcd(fm,l) == 1   #assure qu'il existe exactement deux l-isogénies rationnelles. 

    ql = L.quadratic_form()
    cible = (-ql[1] + f*t)/2   # Forme standard de L              
    (c,d) = base_fq1(cible, fm, dk, f, tracef)   # En particulier d = f est inversible modulo l par hypothèse.
    val = Mod(-c,l)*(Mod(d,l)^(-1))   # Valeur propre du frobenius sur le groupe de L-torsion.  
    val = ZZ(val)
    if abs(val) > abs(val - l):   # La valeur propre est définie modulo l. 
        val = val - l
    
    PFq.<z> = PolynomialRing(Fq)
    Psi = Psi_l(j,z)
    
    print('Recherche de j_invariants')
    racines = Psi.roots()
    assert len(racines) == 2 or racines[0][1] == 2, f"racines was {racines}"
    h = racines[0][0]
    
    if j_prec != None:  #On déduit du calcul précédent que l'un des deux j_invariant correspond au dual/demi-tour.
        if h == j_prec and len(racines) == 2:
            h = racines[1][0]
            
    print('j_invariants trouvés')
    assert h.parent() == E.base_ring()
    
    (A,B) = coeff_courbe_l_isogene(E,l,h,Psi_l)
    E_coef = EllipticCurve(Fq,[A,B])
    print('Choix j_invariant, application BMSS')
    Fker = compute_isogeny_bmss(E, E_coef, l) #On suppose p > 4l + 4 pour appliquer BMSS. 

    print('Verif choix j_invariant')
    if CheckElkies(E, l, Fker, val):
        print('bon j_invariant')
        return Fker
        
    else:  #Peut arriver s'il n'y a pas eu de calculs précédents. 
        print('changement de j_invariant')
        h = racines[1][0]
        (A,B)=coeff_courbe_l_isogene(E,l,h,Psi_l)
        E_coef = EllipticCurve(Fq,[A,B])
        print('Application BMSS')
        Fker = compute_isogeny_bmss(E, E_coef, l)
        if CheckElkies(E, l, Fker, val):
            return Fker
        else:
            raise ValueError('Aucun j_invariant correct') 

def phi_from_L_polynome(E,L,l,q,kq,f,fm,dk,tracef,j,j_prec,Psi_l):

    #Résume ce qui précéde pour déduire d'un idéal de norme l à une isogénie de degré l.
    
    print('Calcul du polynome du noyau')
    F_ker = polynome_ker(E,l,L,f,fm,dk,tracef,j,j_prec,Psi_l)
    print('Calcul isogénie par Vélu')
    phi = E.isogeny(F_ker) 
    return phi


def composantes_de_phi_polynome(E_eval,q,n,kq,Exposant,Idéaux,f,fm,dk,tracef):

    # On calcule une suite d'isogénies données par une listes d'idéaux, chacun affecté d'un exposant.
    
    dépard = E_eval 
    j = dépard.j_invariant()
    j_prec = None
    k = len(Idéaux)
    composantes = []
    PPFq.<X,Y> = PolynomialRing(Fq, order = 'lex')
    for i in [0 .. k-1]:
        Li = Idéaux[i]
        pi = int(Li.norm())
        print('Composante de degré :')
        print(pi)
        Psi_pi = classical_modular_polynomial(pi)  #Acces à une database. Impose pi < 370.
        print('Exposant :')
        print(Exposant[i])  
        j_prec = None
        for i in range(Exposant[i]):
                print('calcul composante numéro', i+1)
                j = dépard.j_invariant()
                phic = phi_from_L_polynome(dépard,Li,pi,q,kq,f,fm,dk,tracef,j,j_prec,Psi_pi)
                composantes.append(phic)
                dépard = phic.codomain()
                j_prec = j
                dépard = EllipticCurve(GF(q^n), [dépard.a4(),dépard.a6()]) #On se replace sur le corps de base pour éviter une escalade d'extensions
    return composantes


#Prise en compte de l'équivalence d'idéaux.


def Coef_equivalent_friable(L,Idéaux,Exposant,D):
    
    #On cherche alpha tel que L = (alpha)*L_friable, où L_friable est décrit pas Idéaux et Exposant
    #On calcule alpha = beta/m, avec beta dans l'ordre de discriminant D, et m entier positif.
    
    B = L     # B sera l'idéal principal dont on cherche un générateur.
    k = len(Idéaux)
    m = 1    # m désigne le produit des normes des idéaux premiers qui factorise L. alpha = beta/m.
    for i in [0 .. k-1] :
        pi = Idéaux[i]
        for _ in range (Exposant[i]):
            B = B*(pi.conjugate())
            m = m*(pi.norm())

    if B.is_principal():    
        beta = (B.gens_reduced())[0]    #Par les formes quadratiques, via une représentation de 1 par la forme quadratique associée à B. 
        bO = NumberFieldOrderIdeal(O,beta)
        if bO == B:
            print('résultat de réduction correct')
            return beta, m
        else:
            print('résultat de réduction conjugué')
            beta = (x - y*t)/2
            return beta, m
    else:
        raise ValueError('Erreur de factorisation')

def eval_phic(P,E_eval,Composantes):
    #On calcule l'image d'un point Q par la composé d'une suite d'isogénies.
    #Q appartient à E_eval, donc peut ne pas être rationnel (si n > 1). 
    dépard = E_eval
    for phi in Composantes:
        P = dépard(P)
        P = phi(P)
        dépard = phi.codomain()
        dépard = EllipticCurve(GF(q^n), [dépard.a4(),dépard.a6()])
    return P

def isom_normalisation(Ec,x,y,m,fm):
    #On calcule l'isomorphisme nécessaire pour normaliser phi. 
    #Il suffit de corriger l'action de [alpha] car les composantes sont normalisées.
    # alpha = (x + y fq )/(fm*m) est précalculé
    u = Fp(x)*((Fp(m*fm))^-1)
    isom = WeierstrassIsomorphism(Ec, (u^(-1), 0, 0, 0))
    return isom

def endo_alpha(Q,En,kq,x,y,m,fm,Cn):
    
    #On veut calculer l'image d'un point Q par l'endomorphisme [alpha].  
    #alpha = (x + y fq)/(mfm)
    
    denom = (Mod(m,Cn)*Mod(fm,Cn))^(-1) # mf_m inversible par choix des nombres premiers depuis le début. 
    c = Mod(x,Cn)*denom
    d = Mod(y,Cn)*denom
    cQ = c*Q      # cQ a bien un sens car c est un entier.
    fqQ = eval_fq(Q,kq,En)
    dfqQ = d*fqQ
    alphaQ = En(cQ) + En(dfqQ) # Ici correction d'un erreur de type inconnue, en précisant que l'on veut additionner des points de En.
    return alphaQ

def Broker_BMSS(E,p,q,kq,E_eval,P,n,K,O,l,N,Borne_z):

    début = time.time()
    #Calcul des données du problème :
    dk = K.discriminant()
    f = O.conductor()
    D = f^2*dk
    
    CE = E.cardinality_pari()
    tracef = E.trace_of_frobenius()
    Dm = tracef^2 - 4*q
    fm = sqrt(Dm/(K.discriminant()))
    
    Cn = E_eval.cardinality()
    test_norm = fm*p*Cn   #On souhaite éviter tout les nombres premiers qui divisent test_norm
    
    #Application des algos précédents :
    
    L = ideal_de_norme(l,f,D)
    
    print('début factorisation')
    Exposant, Idéaux = factorisation(L,D,N,Borne_z,test_norm)
    print('fin factorisation')
    print('temps :')
    print(time.time() - début)
    
    print('début Composantes')
    Composantes = composantes_de_phi_polynome(E_eval,q,n,kq,Exposant,Idéaux,f,fm, dk ,tracef)
    print('fin Composantes')
    print('temps :')
    print(time.time() - début)
    
    beta, m = Coef_equivalent_friable(L,Idéaux,Exposant,D)
    x, y = base_fq1(beta , fm , dk, f,tracef)

    if len(Composantes) > 0:
        Ec = (Composantes[-1]).codomain()
    else:
        Ec = E_eval
    Pc = eval_phic(P,E_eval,Composantes)

    isom = isom_normalisation(Ec,x,y,m,fm)
    Pc = isom(Pc)
    E_phi = isom.codomain()

    Pc = endo_alpha(Pc, E_phi,kq,x,y,m,fm,Cn)
    print(time.time() - début)
    return Pc, E_phi


def Broker_BMSS2(E,p,q,kq,E_eval,P,n,K,O,l,N,Borne_t):

    début = time.time()
    #Calcul des données du problème :
    dk = K.discriminant()
    f = O.conductor()
    D = f^2*dk
    
    CE = E.cardinality_pari()
    tracef = E.trace_of_frobenius()
    Dm = tracef^2 - 4*q
    fm = sqrt(Dm/(K.discriminant()))
    
    Cn = E_eval.cardinality()
    test_norm = fm*p*Cn   #On souhaite éviter tout les nombres premiers qui divisent test_norm
    
    #Application des algos précédents :
    
    L = ideal_de_norme(l,f,D)
    L = L.conjugate()
    
    print('début factorisation')
    Exposant, Idéaux = factorisation_2(L,D,N,Borne_t,test_norm)
    print('fin factorisation')
    print('temps :')
    print(time.time() - début)
    
    print('début Composantes')
    Composantes = composantes_de_phi_polynome(E_eval,q,n,kq,Exposant,Idéaux,f,fm, dk ,tracef)
    print('fin Composantes')
    print('temps :')
    print(time.time() - début)
    
    beta, m = Coef_equivalent_friable(L,Idéaux,Exposant,D)
    x, y = base_fq1(beta , fm , dk, f,tracef)

    if len(Composantes) > 0:
        Ec = (Composantes[-1]).codomain()
    else:
        Ec = E_eval
    Pc = eval_phic(P,E_eval,Composantes)

    isom = isom_normalisation(Ec,x,y,m,fm)
    Pc = isom(Pc)
    E_phi = isom.codomain()

    Pc = endo_alpha(Pc, E_phi,kq,x,y,m,fm,Cn)
    print(time.time() - début)
    return Pc, E_phi



#Exemple Jao small 

p = 10^10 + 19
kq = 1
q = p^kq
Fp = GF(p)
Fq = GF(q)
E = EllipticCurve(Fq, [15,129])

K.<t> = QuadraticField(-38669866235)
O = K.maximal_order()                   #Calculer O et K à partir de E ? CF Sutherland, mais pas d'implementation


f = O.conductor()
D = O.discriminant()

CE = E.cardinality_pari()
tracef = E.trace_of_frobenius()
Dm = tracef^2 - 4*p
fm = sqrt(Dm/(K.discriminant()))

l = 5000000029 #exemple de calcul d'isogénie, cf article


N = 2*int(log(-D,2))^2   #supérieur à 370 : trop grand pour les polynômes modulaires.
N = 370
Borne_t = int(log(-D)/log(log(-D)))
z = 1/(2*sqrt(3))                        
Borne_z = int(sqrt(log(-D/3,2))/z) 

n = 1
Fqn.<xn> = GF(q^n)
E_eval = EllipticCurve(Fqn, [15,129])
P = E_eval(5940782169, 2162385016)

Q , E_phi = Broker_BMSS(E,p,q,kq,E_eval,P,n,K,O,l,N,Borne_z)
print(Q , E_phi)

print('\n')

Q , E_phi = Broker_BMSS2(E,p,q,kq,E_eval,P,n,K,O,l,N,Borne_t)  
print(Q , E_phi)