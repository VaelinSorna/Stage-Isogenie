
from sage.rings.finite_rings.integer_mod import square_root_mod_prime
from sage.rings.finite_rings.integer_mod import square_root_mod_prime_power
from sage.rings.number_field.order_ideal import NumberFieldOrderIdeal
import time

def etude_torsions(E,p,O,K,Nk_max,Nk_min):
    
    rK = K.gens()[0]
    dK = K.discriminant()
    f = O.conductor()
    D = (f^2)*dK
    rD = f*rK
    wK = (dK + rK)/2
    CE = E.cardinality_pari()
    tracef = E.trace_of_frobenius()
    Dm = tracef^2 - 4*p
    fm = sqrt(Dm/(K.discriminant()))
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

    torsions = []
    if Nmax > 2*Nk_min:             #solution à clapoti n'existe pas si N < N1 + N2
        torsions.append([Nmax,1])

    #traces = [tracef]
    #cards = [CE]
    
    frobd = frob
    frob2d = frob2
    q = p
    d = 1
    
    while Nmax < Nk_max^2:
        
        d = d+1
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
            
        Nmax = gcd(a-1,fm/f)
        if Nmax > 2*Nk_min:
            torsions.append([Nmax,d])
        #traces.append(tracefd)
        #cards.append(q + 1 - tracefd)
    
    return torsions, d

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
        return NumberFieldOrderIdeal(O,[l, -sq + f*rK]) #Forme donnée dans le cours de Biasse
    elif kronecker(D,l) == 0:
        return NumberFieldOrderIdeal(O,[l, f*rK])
    else:
        raise "l est inerte"

def ideal_to_element(a,L,O):
    #On suppose a equivalent à L. On cherche alpha dans L tel que a = (alphabar / N(L))L
    assert a.is_equivalent(L)
    B = a*(L.conjugate())
    alphabar = (B.gens_reduced())[0]
    alpha = alphabar.conjugate()
    assert NumberFieldOrderIdeal(O,alphabar) == B
    assert alpha in L
    return alpha

def element_to_ideal(alpha,L,O):
    #On suppose alpha dans L et on lui asocie un idéal equivalent
    assert alpha in L
    alphabar = alpha.conjugate()
    B = NumberFieldOrderIdeal(O,alphabar)
    a2 = B*L
    g1, g2 = a2.gens_reduced()
    a = NumberFieldOrderIdeal(O,[g1/(L.norm()), g2/(L.norm())])
    assert a.is_equivalent(L)
    return a

def base_vecteurs_courts(L,O):    #N'utilise pas LLL. Mieux ?
    f = O.conductor()
    qL = L.quadratic_form()
    rL = qL.reduced_form()
    a = NumberFieldOrderIdeal(O,[rL[0], (-rL[1] + f*rK)/2])
    b = NumberFieldOrderIdeal(O,[rL[2], (rL[1] + f*rK)/2])
    alpha = ideal_to_element(a,L,O)
    beta = ideal_to_element(b,L,O)
    assert NumberFieldOrderIdeal(O,[alpha,beta]) == L  #alpha, beta de normes premier entre elles, donc libre
    return alpha, beta

def liste_premiers_splits(D,borne_B,fm,p):
    #Borne_B: taille maximale des nombres premiers regardés
    liste_B = []
    i = 2
    while i < borne_B :
        if kronecker(D,i) == 1 and i.gcd(fm*p) == 1:
            liste_B.append(i)
        i = next_prime(i)
    return liste_B

def make_liste_ideq(L,O,m,liste_B,CE):
    # m nombre d'idéaux que l'on teste (2m^2)
    # présence de CE : pour evaluer des endomorphismes, on veut des normes premieres avec le cardinal
    # On suppose que l'on ne veut evaluer l'isogenie que sur des points du corps de base Fq.
    
    alpha, beta = base_vecteurs_courts(L,O)
    liste_ideq = []
    Nk_max = 1
    Nk_min = -(O.discriminant())
    ideal_friable = False
    
    for x in [0 .. m]:   #on evite de creer gamma et -gamma
        for y in [-m .. m]:
            if (x != 0 or y > 0):   #on evite les cas x = 0 et y <= 0
                gamma = x*alpha + y*beta
                
                if gamma == 0:
                    raise ValueError('erreur base courte liée') 
                    
                I = element_to_ideal(gamma,L,O)
                NI = I.norm()
                if NI.gcd(CE) != 1:
                    continue
                    
                Nk = NI
                Ne = 1
                Ne_facto = []
                for p in liste_B:
                    exp = 0
                    while Nk%p == 0:
                        exp = exp + 1
                        Nk = Nk/p
                        Ne = Ne*p
                    if exp > 0:
                        Ne_facto.append([p,exp])
                        
                assert NI == Nk*Ne
                if Nk == 1:
                    #print('Ideal equivalent friable', I)
                    ideal_friable = True
                liste_ideq.append([I,Nk,Ne,Ne_facto])
                if Nk > Nk_max:
                    Nk_max = Nk
                if Nk < Nk_min:
                    Nk_min = Nk
                    
    return liste_ideq, Nk_max, Nk_min, ideal_friable

def coin_equation(N1,N2,N):
    
    #On veut résoudre uN1 + vN2 == N dans NN, avec uN1 gcd vN2 == 1 et N divise Nmax
    
    d,u0,v0 = xgcd(N1,N2)
    assert d == 1
    
    if u0 > 0:
        u, v, N, sol = coin_equation(N2,N1,N)
        return v, u, N, sol

    #On suppose u0 <= 0
        
    ku = int(((-u0)*N) // N2) + 1  #erreur de int, etrange ?
    kv = int((v0*N)//N1)
    u = u0*N + ku*N2
    v = v0*N - ku*N1
    assert u*N1 + v*N2 == N

    sol = False
    if ku > kv :
        #print('echec equation dans NN')
        return u, v, N, sol
        
    nb_sols = kv - ku + 1

    while sol == False and nb_sols >= 0:
        duv = u.gcd(v)
        if N%duv != 0:
            continue
        if ((u/duv)*N1).gcd((v/duv)*N2) == 1:
            u = u/duv
            v = v/duv
            N = N/duv
            break
        u = u + N2
        v = v - N1
        nb_sols = nb_sols - 1

    assert u*N1 + v*N2 == N
    if (u*N1).gcd(v*N2) == 1 and v > 0 and u > 0:
        sol = True
            
    return u, v, N, sol


def clapoti_equation(torsions,liste_ideq):
    k_id = len(liste_ideq)
    sols = []
    sols_ext = []
    for i in [0 .. k_id-1]:
        b_prep = liste_ideq[i]
        b, N1, M1, factoM1 = b_prep
        
        for j in [i .. k_id-1]:
            c_prep = liste_ideq[j]
            c, N2, M2, factoM2 = c_prep
            
            if N1.gcd(N2) != 1:
                #print(N1,N2,'echec N1 N2 pas premier entre eux')
                continue

            for Nmax, ext in torsions :
                sol_ext = False
                
                Gcd1 = Nmax.gcd(M1)
                Nmax_loc = Nmax/Gcd1
                Gcd2 = Nmax_loc.gcd(M2)
                Nmax_loc = Nmax_loc/Gcd2
                
                Nmin = N1+N2   
                if Nmin > Nmax_loc :
                    continue
                
                #print('Tentative N =',Nmax_loc, 'N1 =', N1, 'N2 =',N2)
                u,v,N,sol = coin_equation(N1,N2,Nmax_loc)
                if sol:
                    #print('solution :',u,'*',N1,'+',v,'*',N2,'=',N)
                    sols.append([u,N1,v,N2,N,i,j])
                    sol_ext = True
                #else:
                    #print(N,N1,N2,'echec equation')
                if sol_ext == True and ext not in sols_ext:
                    sols_ext.append(ext)

    return sols, sols_ext

def first_solutions_clapoti(prime_max,m_id,l,E,K,O):
    #deg-max : degré d'extension maximal regardé
    #prime_max : taille maximal des nombres premiers considérés petit
    #m_id : interval sur lequel on cherche des idéaux équivalent

    #Renvoie la premiere solution trouvée (plus petite extension possible)

    rK = K.gens()[0]
    dK = K.discriminant()
    f = O.conductor()
    D = (f^2)*dK
    CE = E.cardinality_pari()
    p = E.base_ring().characteristic()
    tracef = p + 1 - CE   #E définie sur Fp
    Dm = tracef^2 - 4*p
    fm = sqrt(Dm/(K.discriminant()))
    
    L = ideal_de_norme(l,f,D)
    
    resultat = []
    liste_B = liste_premiers_splits(D,prime_max,fm,p)
    liste_ideq, Nk_max, Nk_min, ideal_friable = make_liste_ideq(L,O,m_id,liste_B,CE)
    torsions_candidats, deg_max = etude_torsions(E,p,O,K,Nk_max,Nk_min)
    
    for torsion in torsions_candidats:
        sols, sols_ext = clapoti_equation([torsion],liste_ideq)
        if len(sols)>0:
            resultat.append(torsion)
            resultat.append(sols)
            break
    return resultat, liste_ideq, deg_max, ideal_friable

def test_solutions_clapoti(prime_max,m_id,l,E,K,O):
    #prime_max : taille maximal des nombres premiers considérés petit
    #m_id : interval sur lequel on cherche des idéaux équivalent

    #Mesure l'efficacité d'augmenter prime_max
    
    resultat = []
    Bp = 1
    while Bp <= prime_max:
        first, liste_ideq, deg_max, ideal_friable = first_solutions_clapoti(Bp,m_id,l,E,K,O)
        resultat.append([Bp,deg_max,len(liste_ideq),first[0],len(first[1])])
        Bp = next_prime(Bp)
    return resultat

def stat_solutions_clapoti(prime_max, m_id, nb_essais,E,K,O): 

    #Applique l'algorithme first_solution_clapoti en faisant varier les normes l de dépard, un nombre de fois éale à nb_essais. 
    #l est pris au hasard entre 10^20 et 10^21.

    print('prime_max :', prime_max)

    moy_temps = 0
    moy_deg = 0
    moy_id = 0
    nb_id_friable = 0
    max_deg = 0
    min_deg = 0
    D = O.discriminant()

    print('Nombre essais', nb_essais)

    non_friable = 0

    while non_friable < 20 and nb_id_friable < 200:  #valeurs arbitraires

        l = next_prime(randint(10^20, 10^21))
        while kronecker(D,l) != 1:
            l = next_prime(l)
        debut = time.time()
        first, liste_ideq, deg_max, ideal_friable = first_solutions_clapoti(prime_max,m_id,l,E,K,O)
        temps = time.time() - debut

        if ideal_friable:
            print('friable', nb_id_friable)
            nb_id_friable += 1
        else:
            non_friable += 1
            print('non_friable', non_friable)
            deg_sol = first[0][1]
            moy_id = moy_id + len(liste_ideq)
            moy_deg = moy_deg + deg_sol
            moy_temps = moy_temps + temps
            if deg_sol > max_deg:
                max_deg = deg_sol
            if deg_sol < min_deg or min_deg == 0:
                min_deg = deg_sol

    print('temps moyen first solution :',moy_temps/non_friable)
    print('degrés moyen de first solution :', moy_deg/non_friable)
    print('dégrés maximal parmis les solutions :', max_deg)
    print('degrés minimal parmis les solutions :', min_deg)
    print('Nb idéaux théoriques :', m_id*m_id*2 + m_id)
    print('Nb idéaux retenus en moyenne :', moy_id/non_friable)
    print('Nb de tentatives ignorées (idéal friable) :', nb_id_friable)
    print('Fréquence idéaux friables :', nb_id_friable/(nb_id_friable + non_friable) )
    print('\n')

    return 





#Exemple de Jao "small"

print('Exemple JaoSmall')

p = 10^10 + 19
Fp = GF(p)
E = EllipticCurve(Fp, [15,129])

K.<rK> = QuadraticField(-38669866235)
O = K.maximal_order()                   #Calculer O et K à partir de E ? CF Sutherland, mais pas d'implementation


f = O.conductor()
D = O.discriminant()

print('Discriminant =', D)

m_id = isqrt(p.nbits())+1  #choix fait dans Pegasis

prime_max = 370           # taille max polynome modulaire sagemath. Acces Sutherland possible ? 

stat_solutions_clapoti(prime_max, m_id, 20, E,K,O)

prime_max = 1000           # taille max polynome modulaire Sutherland  

stat_solutions_clapoti(prime_max, m_id, 20, E,K,O)




#EXEMPLES Bisson Sutherland

print('Exemple BS1')

#Exemple 1:

p = 1606938044258990275550812343206050075546550943415909014478299
Fp = GF(p)
E = EllipticCurve(Fp,[-3,660897170071025494489036936911196131075522079970680898049528])

K.<rK> = QuadraticField(-7)
f = 524287   #trouver par algo de Sutherland
O = K.order(f*(1 + rK)/2)


print('Discriminant =', D)

m_id = isqrt(p.nbits())+1  #choix fait dans Pegasis

prime_max = 370           # taille max polynome modulaire sagemath. Acces Sutherland possible ? 

stat_solutions_clapoti(prime_max, m_id, 20,E,K,O)

prime_max = 1000           # taille max polynome modulaire Sutherland  

stat_solutions_clapoti(prime_max, m_id, 20,E,K,O)






#Exemple 2:

print('Exemple BS2')

p = 50272551883931021408091448710235646749904660980498576680086699865431843568847
Fp = GF(p)
E = EllipticCurve(Fp,[-3,14262957895783764742987524732821199570860243293007735537575027051453663494306])

K.<rK> = QuadraticField(-7)
f = 852857
O = K.order(f*(1 + rK)/2)


D = O.discriminant()

print('Discriminant =', D)

m_id = isqrt(p.nbits())+1  #choix fait dans Pegasis

prime_max = 370           # taille max polynome modulaire sagemath. Acces Sutherland possible ? 

stat_solutions_clapoti(prime_max, m_id, 20, E,K,O)

prime_max = 1000           # taille max polynome modulaire Sutherland  

stat_solutions_clapoti(prime_max, m_id, 20, E,K,O)






#EXEMPLES Sutherland database

#exemple 1

print('Exemple Sutherland1')

p = 1317860422843322160610398725225958731902944552925978150597
Fp = GF(p)
E = EllipticCurve(Fp,[-3,154344787563346744370152153588767287709323583533485442048])

K.<rK> = QuadraticField(-102197306669747)
O = K.maximal_order()

#Creer par CM. On a f = 1 automatique !
D = O.discriminant()

print('Discriminant =', D)

m_id = isqrt(p.nbits())+1  #choix fait dans Pegasis

prime_max = 370           # taille max polynome modulaire sagemath. Acces Sutherland possible ? 

stat_solutions_clapoti(prime_max, m_id, 20, E,K,O)

prime_max = 1000           # taille max polynome modulaire Sutherland  

stat_solutions_clapoti(prime_max, m_id, 20, E,K,O)





#exemple 2

print('Exemple Sutherland2')

p = 28948022309329048855892746252171992875431396939874100252456123922623314798263
Fp = GF(p)
E = EllipticCurve(Fp,[-3,15325252384887882227757421748102794318349518712709487389817905929239007568605])

K.<rK> = QuadraticField(-10000006055889179)
O = K.maximal_order()

D = O.discriminant()

print('Discriminant =', D)

m_id = isqrt(p.nbits())+1  #choix fait dans Pegasis

prime_max = 370           # taille max polynome modulaire sagemath. Acces Sutherland possible ? 

stat_solutions_clapoti(prime_max, m_id, 20,E,K,O)

prime_max = 1000           # taille max polynome modulaire Sutherland  

stat_solutions_clapoti(prime_max, m_id, 20,E,K,O)
