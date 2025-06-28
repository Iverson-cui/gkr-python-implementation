# sum check protocol
# (to make this a valid noninteractive version of sumcheck, need to use a hash function instead of the random library)
import random
from random import randint

# I ended up just using a fixed prime instead of generating a new one every time. So one needs to change that prime
# value based on the level of security desired. Just change the p variable to a new prime.
first_primes_list = [
    2,
    3,
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
    41,
    43,
    47,
    53,
    59,
    61,
    67,
    71,
    73,
    79,
    83,
    89,
    97,
    101,
    103,
    107,
    109,
    113,
    127,
    131,
    137,
    139,
    149,
    151,
    157,
    163,
    167,
    173,
    179,
    181,
    191,
    193,
    197,
    199,
    211,
    223,
    227,
    229,
    233,
    239,
    241,
    251,
    257,
    263,
    269,
    271,
    277,
    281,
    283,
    293,
    307,
    311,
    313,
    317,
    331,
    337,
    347,
    349,
]

p = 7793


# used to generate a random number of n bits [2** (n - 1) + 1, 2**n - 1]
# this function may have bugs, it should include 2 ** (n-1) and 2 ** n - 1
def nBitRandom(n):
    return random.randrange(2 ** (n - 1) + 1, 2**n - 1)


def getLowLevelPrime(n):
    """
    Generate a prime candidate divisible by first primes

    The returned value is a random prime number of n bits. The prime characteristic is verified by checking with a list of small primes.
    """
    while True:
        # Obtain a random number
        pc = nBitRandom(n)

        # Test divisibility by pre-generated
        # primes
        for divisor in first_primes_list:
            # check divisor up to sqrt(pc) is enough
            if pc % divisor == 0 and divisor**2 <= pc:
                break
        else:
            return pc


def isMillerRabinPassed(mrc):
    """
    higher level prime check function
    Run 20 iterations of Rabin Miller Primality test
    Returns True if mrc is probably prime, False if it is composite.
    """
    maxDivisionsByTwo = 0
    ec = mrc - 1
    while ec % 2 == 0:
        ec >>= 1
        maxDivisionsByTwo += 1
    assert 2**maxDivisionsByTwo * ec == mrc - 1

    def trialComposite(round_tester):
        if pow(round_tester, ec, mrc) == 1:
            return False
        for i in range(maxDivisionsByTwo):
            if pow(round_tester, 2**i * ec, mrc) == mrc - 1:
                return False
        return True

    # Set number of trials here
    numberOfRabinTrials = 20
    for i in range(numberOfRabinTrials):
        round_tester = random.randrange(2, mrc)
        if trialComposite(round_tester):
            return False
    return True


if __name__ == "__main__":
    while True:
        n = 1024
        prime_candidate = getLowLevelPrime(n)
        # prime_candidate is a probably prime number of n bits, only passing initial prime check
        if not isMillerRabinPassed(prime_candidate):
            # But it doesn't pass the Miller-Rabin test, so we need to generate a new one, by saying continue to continue the loop
            continue
        # If it passes the Miller-Rabin test, we can use it as our prime, and assign it to p
        else:
            p = prime_candidate
            break


# Sumcheck needs us to generate bitstrings of length n if our function takes in length-n tuples.
def generate_binary_strings(bit_count):
    """
    given bit_count, this function generates all binary strings combination of that length in a list.
    Notice that it is a string in the list, not integer.
    eg. bit_count = 2 will return ["00", "01", "10", "11"]
    """
    binary_strings = []

    def genbin(n, bs=""):
        if len(bs) == n:
            binary_strings.append(bs)
        else:
            genbin(n, bs + "0")
            genbin(n, bs + "1")

    genbin(bit_count)
    return binary_strings


def Convert(string):
    """
    Convert a string to a list of characters.
    We can simple use list(string) to achieve this
    """
    list1 = []
    list1[:0] = string
    return list1


def sumcheck(value, poly, variable_length):
    """
    value: claimed sum of the polynomial
    poly: polynomial function to be checked
    variable_length: number of variables in the polynomial

    This function implements the sumcheck protocol to verify the claimed sum of a polynomial. At the end, variable_length variables is checked, but without final verification using oracle access.
    """
    if variable_length == 1 and (poly([0]) + poly([1]) % p) == value % p:
        return True

    # g_vector is the vector of evaluations of the polynomial at the random challenge vector r.
    global g_vector
    # r is the random challenge vector. the length of r depends on the variable_length, which is also the round number of the sumcheck protocol
    global r

    g_vector = [0] * (variable_length)
    r = [0] * (variable_length)

    def g_1(x_1):
        # ell means all of the possible assignment combinations of the remaining binary variables in the first round.
        # If there are 3 variables, ell finally will be:[[0,0], [0,1], [1,0], [1,1]]
        # Length of ell: 2 ** (variable_length - 1) because the first variable is fixed to x_1.
        # This function returns the finite field sum of the polynomial evaluated at each binary string in ell.
        ell = generate_binary_strings(variable_length - 1)
        for i in range(len(ell)):
            ell[i] = Convert(ell[i])
            for j in range(len(ell[i])):
                ell[i][j] = int(ell[i][j])

        # insert the value of x_1 into the first position of each binary string in ell
        # if x_1=3, then ell will be [[3,0,0], [3,0,1], [3,1,0], [3,1,1]]
        # together ell means all of the assignment combinations of the first round.
        for i in range(len(ell)):
            ell[i].insert(0, x_1)

        output = 0

        # calculate the sum of the polynomial evaluated at each binary string in ell
        # return output in the finite field
        for i in range(2 ** (variable_length - 1)):
            output += poly(ell[i])
        return output % p

    # first round of sumcheck
    if (g_1(0) + g_1(1)) % p != value:  # first sumcheck check
        return False
    else:
        # first random challenge assigned to r[0]
        r[0] = randint(0, p - 1)
        # g_vector[0] is the evaluation of g_1 at r[0]
        g_vector[0] = g_1(r[0]) % p

    # variable_length - 2 rounds of sumcheck
    for j in range(1, variable_length - 1):  # repeats the steps described above

        def g(x):
            # ell[i] contains all of the assignment combinations of the input variables, including first j random challenges, x in this round, and last binary bits.
            ell = generate_binary_strings(variable_length - j - 1)
            for i in range(len(ell)):
                ell[i] = Convert(ell[i])
                for k in range(len(ell[i])):
                    ell[i][k] = int(ell[i][k])

            for i in range(len(ell)):
                ell[i] = r[0:j] + [x] + ell[i]

            output = 0
            for i in range(len(ell)):
                output += poly(ell[i])
            return output % p

        # compare g(0) and g(1) with the last round result
        if g_vector[j - 1] != (g(0) + g(1)) % p:
            return False
        else:
            # assign this round result
            r[j] = randint(0, p - 1)
            g_vector[j] = g(r[j]) % p

    # Now only the last variable is left to be checked.
    # last round of sumcheck
    def g_v(x_v):
        # Now r is a list of length variable_length, with all but last element assigned.
        eval_vector = r
        # explicitly assign to the last variable of r with input x_v
        eval_vector[variable_length - 1] = x_v
        # return result of the polynomial evaluated at eval_vector
        return poly(eval_vector)

    if (g_v(0) + g_v(1)) % p != g_vector[variable_length - 2]:
        return False
    else:
        r[variable_length - 1] = randint(0, p - 1)
        g_vector[variable_length - 1] = g_v(r[variable_length - 1]) % p
        return True


def get_r():
    return r


# this check isn't actually needed in the gkr protocol, so we don't include it in the sum-check function
# but we add it for completeness.
def lastcheck(poly, x, variable_length, value):
    """
    Final check with the help of oracle access.
    Two things we need to check:
    1. whether the polynomial evaluated at x is equal to the last element of g_vector, which is calculated in the sumcheck function.
    2. whether the sumcheck function returns True, which means the polynomial is correctly evaluated

    Therefore, list r should be assigned to x
    """
    if not sumcheck(value, poly, variable_length) or (
        poly(x) % p != g_vector[variable_length - 1] % p
    ):
        return False
    return True
