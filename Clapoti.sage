
from sage.rings.finite_rings.integer_mod import square_root_mod_prime
from sage.rings.finite_rings.integer_mod import square_root_mod_prime_power
from sage.rings.number_field.order_ideal import NumberFieldOrderIdeal
import time

def etude_torsion(E,p,O,K,Nk_max,Nk_min):  #Correspond à l'algorithme 7 du rapport. 

    #On calcule tout les couples degré-torsion maximale de E, dans l'ordre croissant des degrés, 
    # jusqu'à trouver une torsion supérieur à T_max = (Nk_max)^2.
    #On ignore les couples degré-torsion maximale de E dont la torsion est inférieur à T_min = 2Nk_min.
    
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

    torsion = []
    if Nmax > 2*Nk_min:             #solution à clapoti n'existe pas si N < N1 + N2
        torsion.append([Nmax,1])

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
            torsion.append([Nmax,d])
        #traces.append(tracefd)
        #cards.append(q + 1 - tracefd)
    
    return torsion, d

def ideal_de_norme(l,f,D):

    #Trouver un idéal de norme l premier.
    #On se place dans un ordre de discriminant D et de conducteur f.
    
    if kronecker(D,l) == 1:
        D = Mod(D,l)
        sq = square_root_mod_prime(D,l)
        sm = Mod(-sq,l)
        sq = ZZ(sq)
        sm = ZZ(sm)
        sq = min(sm,sq)
        #print(sq)
        return NumberFieldOrderIdeal(O,[l, -sq + f*rK]) 
    elif kronecker(D,l) == 0:
        return NumberFieldOrderIdeal(O,[l, f*rK])
    else:
        raise "l est inerte"

def ideal_to_element(a,L,O):
    
    #On suppose a equivalent à L. On cherche alpha dans L tel que a = ( (alpha)bar / N(L))L.
    
    assert a.is_equivalent(L)
    B = a*(L.conjugate())
    alphabar = (B.gens_reduced())[0]
    alpha = alphabar.conjugate()
    assert NumberFieldOrderIdeal(O,alphabar) == B
    assert alpha in L
    return alpha

def element_to_ideal(alpha,L,O):
    
    #On suppose alpha dans L et on calcule l'idéal équivalent associé a = ( (alpha)bar / N(L))L.
    
    assert alpha in L
    alphabar = alpha.conjugate()
    B = NumberFieldOrderIdeal(O,alphabar)
    a2 = B*L
    g1, g2 = a2.gens_reduced()
    a = NumberFieldOrderIdeal(O,[g1/(L.norm()), g2/(L.norm())])
    assert a.is_equivalent(L)
    return a

def liste_premiers_splits(D,borne_B,fm,p):

    #On établit une liste de nombres premiers majorés par borne_B, décomposé dans O_D, premiers avec f_m et p. 
    
    liste_B = []
    i = 2
    while i < borne_B :
        if kronecker(D,i) == 1 and i.gcd(fm*p) == 1:
            liste_B.append(i)
        i = next_prime(i)
    return liste_B

def make_liste_ideq(L,O,m,liste_B,CE):   #Correspond à l'algorithme 8 du rapport. On ne calcule pas les factorisations avec parties friables.
    #Pour le calcul de parties friables d'idéaux, voir après les exemples.

    # On établit une liste d'idéaux équivalent à L, de normes minimales, donc on calcule la partie liste_B-friable de la norme.  
    # paramètre m : Le nombre d'idéaux que l'on teste 2m^2 + m. 
    # On ne retient que les idéaux de normes premier avec CE.
    # Si un idéal équivalent de norme friable est trouvé, on s'arrête.

    qL = L.quadratic_form()
    rL = qL.reduced_form()
    RL = NumberFieldOrderIdeal(O,rL)
    
    rK = O.number_field().gens()[0]
    f = O.conductor()
    alpha = rL[0]
    beta = (-rL[1] + f*rK)/2   #N'utilise pas LLL, contrairement à l'implémentation sage de Pegasis.
    
    liste_ideq = []
    Nk_max = 1
    Nk_min = -(O.discriminant())
    ideal_friable = False
    
    for x in [0 .. m]:   
        for y in [-m .. m]:
            if (x != 0 or y > 0):   
                gamma = x*alpha + y*beta    #Pour ne pas creer gamma et -gamma, on evite les cas x < 0, ou (x = 0 et y <= 0), 
                
                if gamma == 0:
                    raise ValueError('erreur base courte liée') #n'est pas censé arriver. 
                    
                I = element_to_ideal(gamma,RL,O)
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
                    ideal_friable = True
                    return [[I,Nk,Ne,Ne_facto]], Nk, Nk, ideal_friable
                    
                liste_ideq.append([I,Nk,Ne,Ne_facto])
                if Nk > Nk_max:
                    Nk_max = Nk
                if Nk < Nk_min:
                    Nk_min = Nk
                    
    return liste_ideq, Nk_max, Nk_min, ideal_friable

def coin_equation(N1,N2,N):   #Correspond à l'algorithme 10 du rapport. 
    
    #On veut résoudre uN1 + vN2 = N dans NN, avec uN1 gcd vN2 == 1 et N divise Nmax
    
    d,u0,v0 = xgcd(N1,N2)
    assert d == 1
    
    if u0 > 0:
        u, v, N, sol = coin_equation(N2,N1,N)
        return v, u, N, sol

    #On suppose u0 <= 0
        
    ku = int(((-u0)*N) // N2) + 1  
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
            nb_sols = nb_sols - 1
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


def clapoti_equation(torsions,liste_ideq):  #Correspond à l'algorithme 9 du rapport. 
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

    # On calcule L un idéal de O de norme l. 
    # Renvoie une solution de l'équation de Clapoti-Pegasis (E,L,prime_max) de degré minimal.  
    # De plus renvoie deg_max le degré maximale considéré lors de l'etude de la torsion.
    # Enfin renvoie ideal_friable = True si un idéal équivalent friable a été trouvé.
    

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

    if ideal_friable:
        return [], liste_ideq, 1, ideal_friable
        
    torsion_candidats, deg_max = etude_torsion(E,p,O,K,Nk_max,Nk_min)
    for torsion in torsion_candidats:
        sols, sols_ext = clapoti_equation([torsion],liste_ideq)
        if len(sols)>0:
            resultat.append(torsion)
            resultat.append(sols)
            break
    return resultat, liste_ideq, deg_max, ideal_friable

def test_solutions_clapoti(prime_max,m_id,l,E,K,O):

    #Applique l'algorithme first_solution_clapoti en faisant varier la borne des nombres premiers entre 1 et prime_max.
    
    resultat = []
    Bp = 1
    while Bp <= prime_max:
        first, liste_ideq, deg_max, ideal_friable = first_solutions_clapoti(Bp,m_id,l,E,K,O)
        if ideal_friable:
            resultat.append([Bp,deg_max,len(liste_ideq),first[0],1])
        else:
            resultat.append([Bp,deg_max,len(liste_ideq),first[0],len(first[1])])
        Bp = next_prime(Bp)
    return resultat

def stat_solutions_clapoti(prime_max, m_id, nb_essais,E,K,O):  #Correspond à l'expérience de la section 6.4.3. 

    #Applique l'algorithme first_solution_clapoti en faisant varier les normes l de dépard, un nombre de fois égale à nb_essais. 
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

    while non_friable < nb_essais and nb_id_friable < 200: #valeur arbitraire

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
f = 524287   
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

#Creer par CM. On a f = 1.
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

#Creer par CM. On a f = 1.
D = O.discriminant()

print('Discriminant =', D)

m_id = isqrt(p.nbits())+1  #choix fait dans Pegasis

prime_max = 370           # taille max polynome modulaire sagemath. Acces Sutherland possible ? 

stat_solutions_clapoti(prime_max, m_id, 20,E,K,O)

prime_max = 1000           # taille max polynome modulaire Sutherland  

stat_solutions_clapoti(prime_max, m_id, 20,E,K,O)
