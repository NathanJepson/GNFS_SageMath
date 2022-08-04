#!/usr/bin/env sage
# coding: utf-8


import ast
import copy
import time

n = 1415960099 #ChangeME
#m = 31 #ChangeME

f = None
d = None
depth = None

a_lb = None
a_ub = None
b_lb = None
b_ub = None

configs = True #Set various variables below using config file config.txt in same directory
find_factor_bases = True #Automatically retrieve factor bases / quadratic character base based on your upper bound size limit
estimate_good_m = True #Get an m that is close to n^(1/d) (you  will need to decide your degree d beforehand)
sieve_size_adjust = True #If not enough bases (solutions) found, incrementally increase sieve size to get more smooth pairs
write_to_output_file = True #Write program output to file
use_depthier_alg_factors = True #FIXME
record_execution_time = True #Record how long it takes for the main chunk of the program to execute (printed at the end)
verbose = False # -------------

rat_factor_base = None
alg_factor_base = None
quad_character_base = None

ub_rat_factor_base = None
ub_alg_factor_base = None
ub_quad_character_base = None

if (configs == True):
    with open("config.txt") as file:
        lines = file.readlines()
        
        for line in lines:
            variable = line.split("=")[0]
            
            if (variable[0] == "#"):
                continue
                
            value = line.split("=")[1]
            
            if (variable == ("n").lower()):
                n = sage.rings.integer.Integer(value)
            elif (variable == ("m").lower()):
                m = sage.rings.integer.Integer(value)
            elif (variable == ("f").lower()):
                f = ast.literal_eval(value)
            elif (variable == ("d").lower()):
                d = sage.rings.integer.Integer(value)
            elif (variable == ("depth").lower()):
                depth = sage.rings.integer.Integer(value)
            elif (variable == ("r_factorbase").lower()):
                rat_factor_base = ast.literal_eval(value)
            elif (variable == ("a_factorbase").lower()):
                alg_factor_base = ast.literal_eval(value)
            elif (variable == ("q_characterbase").lower()):
                quad_character_base = ast.literal_eval(value)
            elif (variable == ("a_lb")):
                a_lb = sage.rings.integer.Integer(value)
            elif (variable == ("a_ub")):
                a_ub = sage.rings.integer.Integer(value)
            elif (variable == ("b_lb")):
                b_lb = sage.rings.integer.Integer(value)
            elif (variable == ("b_ub")):
                b_ub = sage.rings.integer.Integer(value)
            elif (variable == ("ub_rat_factor_base")):
                ub_rat_factor_base = sage.rings.integer.Integer(value)
            elif (variable == ("ub_alg_factor_base")):
                ub_alg_factor_base = sage.rings.integer.Integer(value)
            elif (variable == ("ub_quad_character_base")):
                ub_quad_character_base = sage.rings.integer.Integer(value)
                
        file.close()
        

def BaseMExpansion(n,m):
#Pseudocode of this function at: https://sites.pitt.edu/~bonidie/cs441/Chapter4-2.pdf
    result = []
    q = n
    while (q != 0):
        a = q % m
        q = q // m
        result.append(a)
    return result[::-1] 

def useFunct(f,x,n):
    list2 = f[::-1]
    result = 0
    for i in range(len(list2)):
        if (i == 0):
            result += list2[0]
        else:
            result += list2[i] * power_mod(x,i,n)
    return result

def GetGoodM(n,d):
    
    result = int(n^(1/d))
    
    while ( (n // (result^d)) != 1):
        result-=1
        
    return result

def GetRationalFactorBase(lenRatFactorBase):
    result = []
    currentPrime = 2

    while (len(result) < lenRatFactorBase):
        
        result.append(currentPrime)
        
        if (currentPrime == 2):
            currentPrime = 3
            
        else:
            currentPrime = next_prime(currentPrime + 1)
        
    return result

def GetAlgebraicFactorBase(f,lenAlgFactorBase,d):
    result = []
    currentPrime = 2
    while (len(result) < lenAlgFactorBase):
        countedPrimes = 0
        for r in range(currentPrime + 10):
            if ( (useFunct(f,r,currentPrime) % currentPrime) == 0 and countedPrimes <= d):
                result.append((r,currentPrime))
                countedPrimes+=1
                if (countedPrimes == d):
                    break
        if (currentPrime == 2):
            currentPrime = 3
        else:
            currentPrime = next_prime(currentPrime + 1)
    return result

            
def GetQuadraticCharacterBase(f,lenQuadCharBase,d,alg_factor_base):
    usedPrimes = set()
    result = []
    
    currentPrime = 2
    
    for i in range(len(alg_factor_base)):
        usedPrimes.add(alg_factor_base[i][1])
    
    while (len(result) < lenQuadCharBase):
        countedPrimes = 0
        
        for s in range(currentPrime + 10):
            if (currentPrime in usedPrimes):
                break
                
            if ( (useFunct(f,s,currentPrime) % currentPrime) == 0 and countedPrimes <= d):
                result.append((s,currentPrime))
                countedPrimes+=1
                if (countedPrimes == d):
                    break
        if (currentPrime == 2):
            currentPrime = 3
        else:
            currentPrime = next_prime(currentPrime + 1)
    return result



def compute_integer_product_of_pairs(polynomial_ring, f, m, N, integer_pairs, vector):
        prod  = 1;

        for j in range(len(vector)):
            if (1 == vector[j]):
                prod  = prod*(integer_pairs[j][0] + m*integer_pairs[j][1]) % N;

        return prod;


def find_square(f, beta_squared, polynomial_ring):
    # computes the square root of beta_squared
    # (a polynomial over ZZ of degree less than d, that represents the element in the order ZZ[theta])
    # and returns the polynomial representing the square root.

    K.<a> = NumberField(f);
    beta2 = beta_squared(a);
    if(not beta2.is_square()):
        if (verbose):
            print('The supposedly found square is not square!')
        return False;
    return polynomial_ring(beta2.sqrt().list());


#Modifications to this function from https://web.archive.org/web/20220724010535/https://groups.google.com/g/sage-support/c/LTQjSUDoT8Q
def compute_numberfield_product_of_pairs(polynomial_ring, f, integer_pairs, vector):

    #I = polynomial_ring.ideal(f); #FIXED

    product_polynomial = polynomial_ring([1]);

    for j in range(len(vector)):

        if (1 == vector[j]):

            linear_poly = polynomial_ring([integer_pairs[j][0], integer_pairs[j][1]]);
            product_polynomial = product_polynomial * linear_poly;
            #product_polynomial.mod(I); #FIXED
            product_polynomial = product_polynomial.mod(f) #FIXED

    return product_polynomial;



def compute_difference_of_squares(polynomial_ring, f, m, N, integer_pairs, vector):

    found_squares = False;

    u_plus_v = 0; 
    u_minus_v = 0;
    u = None
    v = None

    ints_mod_N = ZZ.quo(ZZ.ideal(N));

    vsquared = ints_mod_N(compute_integer_product_of_pairs(polynomial_ring, f, m, N, integer_pairs, vector));

    if ( is_square(vsquared)):

        beta_squared = compute_numberfield_product_of_pairs(polynomial_ring, f, integer_pairs, vector);
        beta = find_square(f, beta_squared, polynomial_ring);

        if (False != beta):

            u = (beta(m)) % N;
            v = vsquared.sqrt().lift();

            found_squares = True;

            return (found_squares,beta_squared,beta,u,v);

        else:
            if (verbose):
                print('Failed to find a square root in number field.')
    else:
        if (verbose):
            print('Integer was not square.')

    return (found_squares,'Filler Word.');


def runIt(n,m,f,d,a_lb,a_ub,b_lb,b_ub,depth,lengthRow,rat_factor_base,alg_factor_base,quad_character_base):
    
    r_mat = matrix(0,lengthRow)
    tuples = []
    
    def get_factors():
        pass
    
    for a in range(a_lb,a_ub):
        for b in range(b_lb,b_ub):
            
            if (b == 0):
                continue #Divide-by-zero evasion
                
            r = (a + (b*m))
            r_alg = (power_mod((-1*b),d,n) * (useFunct(f,(a*power_mod(b,-1,n)*-1),n))) % n
            r_alg_2 = abs(r_alg-n)
              
            depth_additions = []
            
            for i in range(depth):
                depth_additions.append(r_alg_2 + (n*(i)))
            
            if (r == 0 or r_alg == 0):
                continue

            r_factors = factor(int(r))

            r_alg_factors = factor(int(r_alg))
            r_alg_factors_depthier = []
            
            for i in range(depth):
                r_alg_factors_depthier.append(factor(int(depth_additions[i])%n)) #Modulo n, fixme?
                
            isIn_rat_fact_base = False
            rat_fact_base_match = True #All r factors are in rational factor base

            isIn_alg_fact_base = False
            alg_fact_base_match = True #All r_alg factors are in algebraic factor base
            
            isIn_depthier_alg_fact_base = False
            depth_alg_fact_base_match = True #All r_alg factors are in one depthier algebraic factor base
            
            for item in r_factors:
                isIn_rat_fact_base = False

                for factorItem in rat_factor_base:
                    if (factorItem == item[0]):
                        isIn_rat_fact_base=True
                        break
                if (not isIn_rat_fact_base):
                    rat_fact_base_match = False
                    break
                    
            if (not (rat_fact_base_match)): #If a + bm factors are not in the rational factor base
                continue
            
            
            for item in r_alg_factors:
                isIn_alg_fact_base = False

                for factorItem in alg_factor_base:
                    if (abs(factorItem[1]) == abs(item[0])): #Using absolute value, FIXME?
                        isIn_alg_fact_base=True
                        break
                        
                if (not isIn_alg_fact_base):
                    alg_fact_base_match = False
                    break
            
            if (not (rat_fact_base_match and alg_fact_base_match)):
                relevantList = None

                for i in range(depth):

                    tmpList = r_alg_factors_depthier[i]

                    for thisFactor in tmpList:
                        isIn_depthier_alg_fact_base = False

                        for factorItem in alg_factor_base:
                            if (abs(factorItem[1]) == abs(thisFactor[0])): #Using absolute value, FIXME?
                                isIn_depthier_alg_fact_base=True
                                break

                        if (not isIn_depthier_alg_fact_base):
                            depth_alg_fact_base_match = False
                            break
                            
                    if (depth_alg_fact_base_match == True):
                        relevantList = copy.deepcopy(tmpList)
                        break
            else:
                depth_alg_fact_base_match = False
            
            if ( (rat_fact_base_match and alg_fact_base_match) or (rat_fact_base_match and depth_alg_fact_base_match)):
                
                if (rat_fact_base_match and depth_alg_fact_base_match):
                    r_alg_factors = copy.deepcopy(relevantList)
                    
                if (r_alg_factors == None):
                    print(r_alg_factors)
                    print('R_alg_factors is none, uh oh!','\n','a:',a,'b:',b,'r_alg:',r_alg)
                    continue
                    
                new_row_r = [0 for j in range(lengthRow)]

                if (r >= 0):
                    new_row_r[0] = 0
                else:
                    new_row_r[0] = 1

                for i in range(len(rat_factor_base)):
                    for j in range(len(r_factors)):
                        if (rat_factor_base[i] == r_factors[j][0]):
                            new_row_r[i+1] = r_factors[j][1]%2
                            break

            
                #Only one such pair can have a ≡ −br (mod p). Such an (r, p) pair is the one
                #...that will be “responsible” for counting the number of times p divides N(a + bθ)
                usedPrimes = set()
                
                for i in range(len(alg_factor_base)):
                    
                    thisR = alg_factor_base[i][0]
                    thisPrime = alg_factor_base[i][1]
                    
                    if (thisPrime in usedPrimes):
                        continue
                    
                    for j in range(len(r_alg_factors)):
                        if (thisPrime == r_alg_factors[j][0]):
                            if ( (a % thisPrime) == (-1*b*thisR)%thisPrime):
                                new_row_r[i+1+len(rat_factor_base)] = r_alg_factors[j][1]%2
                                usedPrimes.add(thisPrime)
                                break
                            
                #counter1 = 0
                for i in range(len(quad_character_base)):
                    s = quad_character_base[i][0]
                    q = quad_character_base[i][1]

                    if (kronecker((a + (b*s)),q) == 1):
                        new_row_r[i+1+len(rat_factor_base)+len(alg_factor_base)] = 0
                        #counter1 += 1
                    elif (kronecker((a + (b*s)),q) == 0):
                        new_row_r[i+1+len(rat_factor_base)+len(alg_factor_base)] = 1
                        #counter1 += 1
                    else:
                        new_row_r[i+1+len(rat_factor_base)+len(alg_factor_base)] = 1
                        #counter1 += 1
                #if (counter1 >= 6):
                #    print('Higher probability.')
                r_mat = r_mat.insert_row(r_mat.nrows(), new_row_r)
                tuples.append((a,b))
                
    if (r_mat.nrows() < lengthRow):
        print('You\'re going to need to increase the sieve size to get about',lengthRow-r_mat.nrows(),'more rows.')
        return r_mat,tuples,False,lengthRow-r_mat.nrows()
    return r_mat,tuples,True


if (record_execution_time == True):
    theTime = (time.time(), time.process_time())
    
if (estimate_good_m):
    assert(d != None) #FIXME!!
    m = GetGoodM(n,d)

R.<x> = ZZ[];
polynomial_ring = R        
    
    
if (f == None):
    f = BaseMExpansion(n,m)
    f_check = polynomial_ring(f[::-1])
    print('The function being used is:',f_check,'\n')
    assert (f_check.is_monic() and f_check.is_irreducible()) #FIXME!!

if (d == None):
    d = len(f)-1

if (ub_rat_factor_base == None or ub_alg_factor_base == None or ub_quad_character_base == None):
    print('Using some default factor base sizes.')
if (ub_rat_factor_base == None):
    ub_rat_factor_base = 15
if (ub_alg_factor_base == None):
    ub_alg_factor_base = 30
if (ub_quad_character_base == None):
    ub_quad_character_base = 9

if (find_factor_bases or (alg_factor_base == None or quad_character_base == None)):
    rat_factor_base = GetRationalFactorBase(ub_rat_factor_base)
    alg_factor_base = GetAlgebraicFactorBase(f,ub_alg_factor_base,d)
    quad_character_base = GetQuadraticCharacterBase(f,ub_quad_character_base,d,alg_factor_base)

print('Rational Factor Base:',rat_factor_base)
print('Algebraic Factor Base:',alg_factor_base)
print('Quadratic Character Base:',quad_character_base,'\n')
    
lengthRow = len(rat_factor_base)+len(alg_factor_base)+len(quad_character_base)+1

error = False

if (a_lb == None or a_ub == None or b_lb == None or b_ub == None):
    print('Using some default bounds for sieving interval.')
if (a_lb == None):
    a_lb = -1000
if (a_ub == None):
    a_ub = 1000
if (b_lb == None):
    b_lb = 1
if (b_ub == None):
    b_ub = 60

print('Sieving to find more than',lengthRow,'smooth pairs.')
result = runIt(n,m,f,d,a_lb,a_ub,b_lb,b_ub,depth,lengthRow,rat_factor_base,alg_factor_base,quad_character_base)
r_mat = result[0]
tuples = result[1]

print(len(tuples),'total smooth pairs found.')

M = matrix(GF(2), len(tuples), r_mat)
solutions = M.kernel().basis_matrix().rows();

print(len(solutions),'total bases found.')
print('\n')

nonTrivialFactorizations = 0

if (result[2] == True or len(solutions) > 0):
    
    f = polynomial_ring(f[::-1])
    
    for i in range(len(solutions)):

        tempRow = solutions[i]

        integer_pairs = tuples
        vector = tempRow

        result = compute_difference_of_squares(R,f,m,n,integer_pairs,vector)

        if (result[0] == True):
            u = result[3]
            v = result[4]

            if (u != v):
                if (gcd(n,u+v) != 1 and gcd(n,u+v) != n):
                    if (verbose):
                        print(result)
                    else:
                        print('Square Root 1:',result[3],'Square Root 2:',result[4])
                    print('Factors are:',gcd(n,u-v),'and',gcd(n,u+v))
                    nonTrivialFactorizations += 1
                else:
                    if (verbose):
                        print('Trivial factorization found: u=',u,'v=',v,'gcd(n,u-v) =',1,'and','gcd(n,u+v) =',n)
            else:
                if (verbose):
                    print('Trivial factorization found:',u,',',v)

print('\n')
print('Non-trivial factorizations:',nonTrivialFactorizations)
if (record_execution_time == True):
    theTime2 = (time.time(), time.process_time())
    print('Elapsed seconds:',theTime2[0]-theTime[0])
    print('Elapsed CPU time:',theTime2[1]-theTime[1])
