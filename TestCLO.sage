from sage.rings.finite_rings.integer_mod import square_root_mod_prime
from sage.rings.finite_rings.integer_mod import square_root_mod_prime_power
from sage.rings.number_field.order_ideal import NumberFieldOrderIdeal
import time
import numpy as np 

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

#La racine utilisée ici n'est pas le coefficient b de la forme quadratique associée.



def forme_de_norme(l,D):

    #Remarque : Seysen dmande une racine spécifique, la plus petite vu dans N. Mais cela n'est pas nécessaire pour la suite (Cf Cohen)
    
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
        ql = BinaryQF([l,b, (b^2 - D)/(4*l)])
        if ql.discriminant() == D:
            return ql
        else:
            raise ValueError('erreur de discriminant de forme')



def formes_generatrices (D,N,test_norm): #Trouver la borne : Analyse de Jao

#Algo 2 Jao : Trouver une famille génératrice du groupes de classes, vu comme formes quadratiques réduites,
# En n'utilisant que des idéaux de normes premiers petits splits et autorisés pour le calcul d'isogénies horizontales
# On génére simplement une famille de N idéaux, N supposé suffisament grand pour que leurs classes soient génératrices.
# Seysen partie 3 : N = 2log^2(D) suffirait (Admet Riemann Généralisé)
    
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



def facto_complet(a,Primes):
    
    #On veut savoir si un entier a de factorisation facto = factor(a) ne contient que des premiers de la liste Primes
    # On utilise le fait que facto et Primes soit triée

    test = a
    k = len(Primes)
    for i in [0 .. k-1]:
        pi = Primes[i]
        while test%pi == 0:
            test = test/pi
    return test == 1




def factorisation(L,D,N,Borne_z,test_norm):

    #Algo 3 Jao : (Hafney / McCurley) Factoriser L dans la base précédente
    #On cherche au hasard à ramener la classe de L à une classe simplifiable par le théorème 3.1 de Seysen.
    #On représente les classes par des formes quadratiques réduites : c'est nécessaire pour se ramener à Seysen
    #Borne_z est une borne donnée par Jao dans l'analyse de l'algorithme. Le nombres de facteurs de L ne dépassera pas Borne_z
    
    Idéaux, Formes, Primes = formes_generatrices (D,N,test_norm)
    ql = (L.quadratic_form()).reduced_form() #Représente la classe de L
    k = len(Primes)
    
    a = ql[0]
    
    relation = ql        # Partant de ql, on va chercher une classe simplifiable
    
    expx = [0]*k
    liste_indice = []
    compte = 0
    while facto_complet(a,Primes) == False:
        compte = compte + 1
        # Choix d'exposant au hasard, on veut entre 3 et Borne_z coefficient non nul (Cf algo 3 Jao)
        # Autoriser 1 ou 2 comme nombre d'exposant possible ?
        
        expx = [0]*k       # La liste des exposants notée xi par Jao
        nb_indice = randint(3,Borne_z) 
        liste_indice = []    # on choisit les idéaux qui vont intervenir dans la factorisation, au hasard.
        while len(liste_indice) < min(nb_indice,k):
            i = randint(0,k-1)
            if i not in liste_indice :
                liste_indice.append(i)
        
        
        for i in liste_indice:
            expi = randint(1,int((N/Primes[i])^2))   #On attribue à chaque indice un exposant xi, bornée d'après Jao.
            expx[i] = expi

        
        # calcul de ql*( fi^exp(xi) pour tout i ) pour chercher une relation "simplifiable"
        relation = ql
        for i in [0 .. k-1]:
            for _ in [1 .. (expx[i])]:
                relation = (relation*Formes[i]).reduced_form()
        a = relation[0] #Si a factorise complétement dans Primes, c'est gagné avec Seysen
        
    facto = factor(a) 
    
    
    #Calcul des valuations de a en chaque Primes, et change le signe selon la méthode Seysen
    expu = [0]*k     #liste des exposant ui de Jao
    ka = len(facto)
    b = relation[1]
    j = 0
    for i in [0 .. k-1]:
        if j < ka :
            if Primes[i] == facto[j][0] :  
                expu[i] = facto[j][1]
                bi = Formes[i][1]
                if Mod( b , 2*Primes[i]) != Mod( bi , 2*Primes[i]):
                    expu[i] = -expu[i]
                j = j + 1
        
    
    #inverser la relation pour trouver L:
    
    expe = []     #liste des exposants ei de Jao
    factoL = []
    for i in [0 .. k-1] :
        ei = expu[i] - expx[i]
        if ei > 0 :
            expe.append(ei)
            factoL.append(Idéaux[i])
        elif ei < 0 :
            expe.append(-ei)
            factoL.append(Idéaux[i].conjugate())
            
    
    return expe, factoL , compte



# Version 2 de la factorisation : avec une borne version Biasse / Graphe expanseur

def factorisation_2(L,D,N,Borne_t,test_norm):

    #Algo 3 Jao : (Hafney / McCurley) Factoriser L dans la base précédente
    #On cherche au hasard à ramener la classe de L à une classe simplifiable par le théorème 3.1 de Seysen.
    #On représente les classes par des formes quadratiques réduites : c'est nécessaire pour se ramener à Seysen
    #Borne_z est une borne donnée par Jao dans l'analyse de l'algorithme. Le nombres de facteurs de L ne dépassera pas Borne_z
    
    Idéaux, Formes, Primes = formes_generatrices (D,N,test_norm)
    ql = (L.quadratic_form()).reduced_form() #Représente la classe de L
    k = len(Primes)
    a = ql[0]
    Min_reduction = int(sqrt(-D/3))
    relation = ql        # Partant de ql, on va chercher une classe simplifiable

    expx = [0]*k
    liste_indice = []
    compte = 0
    while facto_complet(a,Primes) == False:
        compte = compte + 1
        # Choix d'exposant au hasard, on veut entre 3 et Borne_z coefficient non nul (Cf algo 3 Jao)
        # Autoriser 1 ou 2 comme nombre d'exposant possible ?
        
        expx = [0]*k   
        test = ql[0]
        for i in [1 .. Borne_t]:
            indice = randint(0,k-1)
            increment = randint(0,1)
            if increment == 0:
                increment = -1
            expx[indice] = expx[indice] + increment
            test = test*Primes[indice]
        #print('Test si reduction ? :', test >= Min_reduction)
            
        # calcul de ql*( fi^exp(xi) pour tout i ) pour chercher une relation "simplifiable"
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
        
    facto = factor(a) 
    
    
    #Calcul des valuations de a en chaque Primes, et change le signe selon la méthode Seysen
    expu = [0]*k     #liste des exposant ui de Jao
    ka = len(facto)
    b = relation[1]
    j = 0
    for i in [0 .. k-1]:
        if j < ka :
            if Primes[i] == facto[j][0] :  
                expu[i] = facto[j][1]
                bi = Formes[i][1]
                if Mod( b , 2*Primes[i]) != Mod( bi , 2*Primes[i]):
                    expu[i] = -expu[i]
                j = j + 1
        
    
    #inverser la relation pour trouver L:
    
    expe = []     #liste des exposants ei de Jao
    factoL = []
    for i in [0 .. k-1] :
        ei = expu[i] - expx[i]
        if ei > 0 :
            expe.append(ei)
            factoL.append(Idéaux[i])
        elif ei < 0 :
            expe.append(-ei)
            factoL.append(Idéaux[i].conjugate())
            
    
    return expe, factoL, compte


def test(K,O,l,N,Borne_z,Borne_t):
    
    
    dk = K.discriminant()
    f = O.conductor()
    D = f^2*dk
    
    L = ideal_de_norme(l,f,D)
    # On choisit test_norm de sorte toujours commencer une marche aléatoire
    ql = L.quadratic_form()
    print(ql)
    ql = ql.reduced_form()
    print(ql)
    test_norm = ql[0]
    print('test_norm :', test_norm)
    
    début = time.time()
    Exposant, Idéaux, Compte = factorisation(L,D,N,Borne_z,test_norm)
    t1 = time.time() - début

    début = time.time()
    Exposant2, Idéaux2, Compte2 = factorisation_2(L,D,N,Borne_t,test_norm)
    t2 = time.time() - début

    return Exposant, t1, Compte, Idéaux, Exposant2, t2, Compte2, Idéaux2




D = -3635657473823

K.<t> = QuadraticField(D)
O = K.maximal_order()
D = O.discriminant()

print('Discriminant ordre :', D)

N = 2*int(log(-D,2))^2                 
z = 1/(2*sqrt(3))  
Borne_z = int(sqrt(log(-D/3,2))/z)     
Borne_t = int(log(-D)/log(log(-D)))

l = next_prime(randint(10^20, 10^21))
while kronecker(D,l) != 1:
        l = next_prime(l)

somme_exp = []
temps = []
tentatives = []
nb_idéaux = []
norme_max = []
nb_exp = []

somme_exp2 = []
temps2 = []
tentatives2 = []
nb_idéaux2 = []
norme_max2 = []
nb_exp2 = []

for i in range(30):
    exp1, t1, c1, Id1, exp2, t2, c2, Id2 = test(K,O,l,N,Borne_z,Borne_t)
    temps.append(t1)
    temps2.append(t2)
    tentatives.append(c1)
    tentatives2.append(c2)
    somme_exp.append(sum(exp1))
    somme_exp2.append(sum(exp2))
    nb_idéaux.append(len(Id1))
    nb_idéaux2.append(len(Id2))
    norme_max.append((Id1[-1]).norm())
    norme_max2.append((Id2[-1]).norm())

print('Somme des exposants :')
print(np.mean(somme_exp), np.mean(somme_exp2))
print('temps de calcul :')
print(np.mean(temps), np.mean(temps2))
print('nombre de tentatives :')
print(np.mean(tentatives), np.mean(tentatives2))
print('nombre exposants :')
print(np.mean(nb_idéaux), np.mean(nb_idéaux2))
print('norme maximale :')
print(np.mean(norme_max), np.mean(norme_max2))




