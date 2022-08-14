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
        for r in range(currentPrime + 1):
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
        
        for s in range(currentPrime + 1):
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
    
    rational_remainingPrimes = set()
    rational_remainingPrimes2 = set()
    rational_remainingPrimes3 = set()
    
    def get_factors(numA,algebraic=False):
        result = []
        len_divisors = None
        
        if (algebraic):
            len_divisors = len(alg_factor_base)
        else:
            len_divisors = len(rat_factor_base)
            
        for i in range(len_divisors):
            if (numA == 1):
                break
                
            if (algebraic):
                thisFactor = alg_factor_base[i][1]
            else:
                thisFactor = rat_factor_base[i]
                
            exponent_tracker = 0
            
            while(thisFactor.divides(numA)):
                    
                exponent_tracker += 1
                numA = numA // thisFactor
                
            if (exponent_tracker > 0):
                result.append((thisFactor,exponent_tracker))
                
        
        if (numA != 1 and is_prime(numA) and (not algebraic)):
            if (numA in rational_remainingPrimes):
                if (numA in rational_remainingPrimes2):
                    rational_remainingPrimes3.add(numA)
                else:
                    rational_remainingPrimes2.add(numA)
            else:
                rational_remainingPrimes.add(numA)
                
        CompletelyFactored = False
        
        if (numA == 1):
            CompletelyFactored = True
        
        return result,CompletelyFactored
    
    
        
    for a in range(a_lb,a_ub):
        for b in range(b_lb,b_ub):
                
            r = (a + (b*m))
            r_alg = (power_mod((-1*b),d,n) * (useFunct(f,(a*power_mod(b,-1,n)*-1),n))) % n
            r_alg_2 = abs(r_alg-n)
            
            if (r == 0 or r_alg == 0):
                continue
                
            depth_additions = []
            
            for i in range(depth):
                depth_additions.append(r_alg_2 + (n*(i)))
            
            factor_r = get_factors(int(r))
            r_factors = factor_r[0]
            rat_fact_base_match = factor_r[1] #Completely factored over the rational factor base
            if (not rat_fact_base_match): #If a + bm factors are not in the rational factor base
                continue
            
            factor_r_alg = get_factors(int(r_alg),True)
            r_alg_factors = factor_r_alg[0]
            alg_fact_base_match = factor_r_alg[1] #If a + bθ factors completely over the algebraic factor base
        
            depth_alg_fact_base_match = False #All r_alg factors are in one depthier algebraic factor base
            
            if (not alg_fact_base_match):
                for i in range(depth):
                    get_r_alg_depthier_factors = get_factors(int(depth_additions[i])%n,True)
                    r_alg_depth_factors = get_r_alg_depthier_factors[0]
                    depth_alg_fact_base_match = get_r_alg_depthier_factors[1]
                    
                    #r_alg_factors_depthier.append(factor(int(depth_additions[i])%n)) #Modulo n, fixme?
                    #r_alg_factors_depthier.append(r_alg_depth_factors)
                    
                    if (depth_alg_fact_base_match):
                        r_alg_factors = r_alg_depth_factors
                        break
                
            if (not (alg_fact_base_match or depth_alg_fact_base_match)): #If a + bθ is not factorable over any algebraic factor base
                continue
            

            #if (r_alg_factors == None):
            #    print(r_alg_factors)
            #    print('R_alg_factors is none, uh oh!','\n','a:',a,'b:',b,'r_alg:',r_alg)
            #    continue
            assert(r_alg_factors != None) #FIXME 

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


            usedPrimes = set()
            thisPrime = None
            for i in range(len(alg_factor_base)):

                thisR = alg_factor_base[i][0]
                thisPrime = alg_factor_base[i][1]

                #"A first degree prime ideal represented by the pair (r, p) divides <a + bθ> if and only if p
                #....divides N(a + bθ), which occurs if and only if a ≡ −br (mod p)"
                #.......
                #"Only one such pair can have a ≡ −br (mod p). Such an (r, p) pair is the one
                #...that will be “responsible” for counting the number of times p divides N(a + bθ)"
                #...--Matthew E. Briggs
                for j in range(len(r_alg_factors)):
                    if (thisPrime == r_alg_factors[j][0]):
                        if (thisPrime in usedPrimes):
                            if ( (a % thisPrime) == (-1*b*thisR)%thisPrime):
                                new_row_r[i+1+len(rat_factor_base)] = r_alg_factors[j][1]%2
                                #Unsure if I should comment this line out based on the "only one" comment from Briggs above      
                        else:
                            if ((a % thisPrime) == (-1*b*thisR)%thisPrime):
                                new_row_r[i+1+len(rat_factor_base)] = r_alg_factors[j][1]%2
                                usedPrimes.add(thisPrime)

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

            #if (counter1 >= SOME_THRESHOLD):
            #    print('Higher probability.')

            r_mat = r_mat.insert_row(r_mat.nrows(), new_row_r)
            tuples.append((a,b))
                
                
    if (r_mat.nrows() < lengthRow):
        print('You\'re going to need to increase the sieve size to get about',lengthRow-r_mat.nrows(),'more rows.')
        return r_mat,tuples,False,lengthRow-r_mat.nrows(),rational_remainingPrimes2,rational_remainingPrimes3
    return r_mat,tuples,True,rational_remainingPrimes2,rational_remainingPrimes3


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
remainingPrimes3 = result[-1]
remainingPrimes2 = result[-2]

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
                    

f = open("more_rational_factorbase_primes.txt", "w")
#print('More primes you could\'ve added to the rational factor base:')
f.write('More primes you could\'ve added to the rational factor base:')
#print('Strong candidates:')
f.write('\n')
f.write('Strong candidates:')
#print('\n')
f.write('\n')
for x in remainingPrimes3:
    f.write(str(x)+'\n')
    #print(x,end=" ")
#print('Mediocre candidates:')
for x in remainingPrimes2:
    f.write(str(x)+'\n')
#    print(x,end=" ")
f.close()

print('Non-trivial factorizations:',nonTrivialFactorizations)

if (record_execution_time == True):
    theTime2 = (time.time(), time.process_time())
    print('Elapsed seconds:',theTime2[0]-theTime[0])
    print('Elapsed CPU time:',theTime2[1]-theTime[1])
