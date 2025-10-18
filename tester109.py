# Automated tester for the problems in the collection
# "109 Python Problems for CCPS 109" by Ilkka Kokkarinen.
# Report errors and improvements to ilkka.kokkarinen@gmail.com

# Requires Python 3.7+ for the guarantee to iterate collections
# in the insertion order, needed to run some test case generators
# the exact same way in every platform and future Python version.

from hashlib import sha256
from time import time
from itertools import islice, permutations, combinations, zip_longest, cycle, product, count, chain
from math import isqrt, gcd
from random import Random
import gzip
import os.path
import string
from sys import version_info, exit
import labs109
from fractions import Fraction as F
from datetime import date

# During development, this dictionary contains the functions whose calls and
# results you want to see first during the test run. Make each entry "name":N,
# where N is how many test cases you want to see printed out. This also makes
# the tester to run the tests for these functions first, regardless of their
# position in the labs109.py file. Use the limit of -1 to say "all test cases".

# ZZZ

verbose_execution = {
    #   "function_one": 42,   # Print the first 42 test cases of function_one
    #   "function_two": -1,   # Print all test cases of function_two, however many there are
    #   "function_three": 0   # Be silent with function_three (but run it early)
}

# Whether to use the expected answers from the expected answers file when they exist.
use_expected_answers = True

# The release date of this version of the tester.False
version = "October 18, 2025"

# Fixed seed used to generate pseudorandom numbers.
fixed_seed = 12345

# Name of the file that contains the expected answers.
expected_answers_file = 'expected_answers'

# Markers used to separate the parts of the expected answers file.
# These should never appear as the prefix of any expected answer.
version_prefix = '<$$$$>'
function_prefix = '<****>'

# Timeout cutoff for individual function tests, in seconds.
timeout_cutoff = 20

# How many test cases to record in the file for each function.
testcase_cutoff = 300

# Is the script allowed to create a new expected_answers file? Do not
# change this unless you know what you are doing.
can_record = False

# For instructors who want to add their own problems to this set:
#
# 1. Set the value of use_record to False. Update the version info
#    of this tester script in the above settings.
# 2. Write your private solution function to your model solutions
#    file labs109.py.
# 3. Write the corresponding test case generator in this script below.
# 4. Add the individual test into the list of testcases list below,
#    using None as its expected checksum for the moment.
# 5. Run this test script.
# 6. Replace None in the test case with the printed checksum.
# 7. Run this test script again to make sure the test passes.
# 8. Once you have done the above for all the functions that you
#    want to add, set the value of use_record back to True.
# 9. Delete the expected_answers file from the same folder that
#    this script is located in.
# 10. Run this test script to generate the new expected answers file.
# 11. Release the new version of tester and record to students.


# Convert a dictionary or set result to a list sorted by keys to
# guarantee that such results are identical in all environments.

def canonize(result):
    if isinstance(result, dict):
        result = [(key, result[key]) for key in result]
        result.sort()
    elif isinstance(result, set):
        result = [key for key in result]
        result.sort()
    return result


# Convert the arguments given to the student function into a string for safekeeping,
# just in case the student function messes up the contents of the argument objects.
# This makes the discrepancy outputs accurate and less confusing to students. Also,
# when arguments are long, we will try not to flood the user console.

def stringify_args(args, cutoff=2000):
    result = ""
    for (i, a) in enumerate(args):
        if i > 0:
            result += ", "
        if type(a) == list or type(a) == tuple:
            if len(a) < cutoff:
                result += str(a)
            else:
                left = ", ".join([str(x) for x in a[:5]])
                right = ", ".join([str(x) for x in a[-5:]])
                result += f"[{left}, <{len(a) - 10} omitted...>, {right}]"
        else:
            result += repr(a) if len(repr(a)) < cutoff else '[...]'
    return result


# Runs the function f for its test cases, calculating SHA256 checksum
# for the results. If the checksum matches the expected, return the
# running time, otherwise return -1. If expected == None, print out
# the computed checksum instead. If recorder != None, print out the
# arguments and the result returned from function into the recorder.

def test_one_function(f, test_generator, expected_checksum=None, recorder=None, expected_answers=None):
    function_name, recorded, output_len = f.__name__, None, 0
    print(f"{function_name}: ", end="", flush=True)
    # How many results of function calls to print out.
    verb_count = verbose_execution.get(function_name, 0)
    if recorder:
        print(f"{function_prefix}{function_name}", file=recorder)
    if expected_answers:
        recorded = expected_answers.get(function_name, None)
    chk, start_time, crashed = sha256(), time(), False
    for (test_case_idx, test_args) in enumerate(test_generator(fixed_seed)):
        # Convert a singleton of any non-tuple into singleton tuple.
        if not isinstance(test_args, tuple):
            test_args = (test_args,)
        # Convert arguments to a string for safekeeping in case of discrepancy.
        test_args_string = stringify_args(test_args)
        # Call the function to be tested with the arguments from the test tuple.
        try:
            result = f(*test_args)
        except Exception as e:  # catch any exception
            crashed = True
            print(f"CRASH AT TEST CASE #{test_case_idx} WITH ARGS: {test_args_string}")
            print(f"CAUGHT EXCEPTION: {e}")
            break
        # If the result is a set or dictionary, turn it into sorted list first.
        result = canonize(result)
        # Print out the argument and result, if in verbose mode.
        if verb_count > 0 or verb_count == -1:
            verb_count -= 1 if verb_count > 0 else 0
            print(f"{function_name} #{test_case_idx}: ", end="", flush=True)
            print(test_args_string)
            print(f"RESULT: {result}", flush=True)
        # Update the checksum.
        sr = str(result)
        chk.update(sr.encode('utf-8'))
        # When in recording mode, write the answer to the record file.
        if recorder:
            output = sr.strip()
            print(output, file=recorder)
            output_len += len(output) + 1
            if test_case_idx >= testcase_cutoff:
                break
        if use_expected_answers and expected_answers and test_case_idx < testcase_cutoff and recorded:
            if sr.strip() != recorded[test_case_idx]:
                crashed = True
                print(f"DISCREPANCY AT TEST CASE #{test_case_idx}: ")
                print("ARGUMENTS: ", end="")
                print(test_args_string)
                print(f"EXPECTED: {recorded[test_case_idx]}")
                print(f"RETURNED: {sr}")
                break
        total_time = time() - start_time
        if total_time > timeout_cutoff:
            print(f"TIMEOUT AFTER TEST CASE #{test_case_idx}. FUNCTION REJECTED AS TOO SLOW.")
            crashed = True
            break
    if not recorder:
        total_time = time() - start_time
        digest = chk.hexdigest()
        if not crashed and not expected_checksum:
            print(digest)  # Expected checksum for the instructor to copy-paste
            return total_time
        elif not crashed and digest[:len(expected_checksum)] == expected_checksum:
            print(f"Success in {total_time:.3f} seconds.")
            return total_time
        elif crashed:
            return -1
        else:
            print("CHECKSUM MISMATCH: AT LEAST ONE ANSWER WAS WRONG.")
            print("YOUR FUNCTION HAS SOME EDGE CASE BUG THAT DID NOT MANIFEST")
            print(f"IN THE FIRST {testcase_cutoff} TEST CASES. IF YOU CAN'T FIND THIS")
            print("BUG AFTER SLEEPING OVER IT ONCE, PLEASE SEND YOUR FUNCTION")
            print("TO ilkka.kokkarinen@gmail.com TO HELP IMPROVE THE QUALITY OF")
            print(f"THESE AUTOMATED TEST CASES. ENSURE THAT YOUR {function_name}")
            print("DOES NOT USE ANY FLOATING POINT CALCULATIONS WHOSE PRECISION")
            print("RUNS OUT ONCE THE NUMBERS INVOLVED BECOME LARGE ENOUGH.")
            return -1
    else:
        print(f"({output_len}) ")
        return 0


# Sort the suite of test cases according to the order in which
# they appear in the student source code.

def sort_by_source():
    funcs, recognized = dict(), set(f for (f, _, _) in testcases)
    need_check = [f for (f, test, check) in testcases if check is None]
    with open('labs109.py', 'r', encoding='utf-8') as source:
        for (line_no, line) in enumerate(source):
            if line.startswith("def "):
                function_name = line[4:line.find('(')].strip()
                if function_name in funcs:  # Who knows how many future students this will save.
                    print(f"WARNING: MULTIPLE DEFINITION FOR {function_name}")
                if function_name in recognized:
                    funcs[function_name] = 0 if function_name in verbose_execution or function_name in need_check else line_no
        testcases.sort(key=lambda x: funcs.get(x[0], 9999999))
    return sorted(funcs.keys())


# Runs the tests for all functions in the suite, returning the
# count of how many of those were implemented and passed the test.

def test_all_functions(module, recorder=None, known=None):
    if recorder:
        print("\nRECORDING THE RESULTS OF INSTRUCTOR MODEL SOLUTIONS.")
        print("IF YOU ARE A STUDENT, YOU SHOULD NOT BE SEEING THIS")
        print(f"MESSAGE!!! ENSURE THAT THE FILE {expected_answers_file} FROM")
        print("WHEREVER YOU DOWNLOADED THIS AUTOMATED TESTER IS ALSO")
        print("PROPERLY PLACED IN THIS VERY SAME WORKING DIRECTORY!!!\n")
        print(f"Recording {testcase_cutoff} test cases per problem.\n")
    accepted_count, total = 0, 0
    if recorder:
        print(f"{version_prefix}{version}", file=recorder)
    for (f_name, test_cases, expected) in testcases:
        try:
            f = module.__dict__[f_name]
        except KeyError:
            continue
        total += 1
        result = test_one_function(f, test_cases, expected, recorder, known)
        if result >= 0:
            accepted_count += 1
    if recorder:
        print("\nRecording model answers complete.")
    else:
        print(f"{accepted_count} out of {total} functions ", end="")
        print(f"of {len(testcases)} possible work.")
    return accepted_count


# Named constants used by some test case generators.

ups = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
lows = "abcdefghijklmnopqrstuvwxyz"

__primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101]

__names = [
    "hu", "oh", "eye", "kro", "atz", "put",
    "ross", "rachel", "monica", "phoebe", "joey", "chandler",
    "johndorian", "elliot", "turk", "carla", "perry", "bob",
    "eddie", "joy", "jeff", "steph", "allison", "doug",
    "jules", "ellie", "laurie", "travis", "grayson", "andy",
    "donald", "melania", "hillary", "barack", "bill", "kamala",
    "mxuzptlk", "ouagadougou", "oumoumou", "auervaara",
    "britain", "germany", "france", "canada", "exit",
    "urban", "zuauaua", "aueiosh", "knickerbocker",
    "keihanaikukauakahihuliheekahaunaele",
    "llanfairpwllgwyngyllgogerychwyrndrobwllllantysiliogogogoch"
]

__knight_moves = [(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]

# Some utility functions to help writing test generators.

# Produce an infinite sequence of exponentially increasing integers.
# The parameters scale and skip determine how quickly the sequence grows.


def scale_random(seed, scale, skip):
    # The seed value determines the future random sequence.
    rng = Random(seed)
    curr, count_until_increase, orig = 1, 0, scale
    while True:
        curr += rng.randint(1, scale)
        yield curr
        count_until_increase += 1
        if count_until_increase == skip:
            scale = scale * orig
            count_until_increase = 0


# Produce a random (n+1)-digit integer with adjustable repeating digits.

def random_int(rng, n, prob=70):
    r, curr = 0, rng.randint(1, 9)
    for _ in range(n):
        r = 10 * r + curr
        if rng.randint(0, 99) < prob:
            curr = rng.randint(0, 9)
    return r


# Create a random n-character string from the given alphabet.

def random_string(alphabet, n, rng):
    result = ''
    for _ in range(n):
        result += rng.choice(alphabet)
    return result


# The pyramid series is handy for yielding test case lengths in the
# manner of 1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, ...

def pyramid(n=1, goal=5, inc=1):
    count_until_increase = 0
    while True:
        yield n
        count_until_increase += 1
        if count_until_increase == goal:
            goal, count_until_increase, n = goal + inc, 0, n + 1


# Rearrange the numbering of graph given in adjacency list form.

def rearrange_graph(edges, rng):
    n = len(edges)
    perm = list(range(n))
    rng.shuffle(perm)
    new_edges = [[] for _ in range(n)]
    for u in range(n):
        for v in edges[u]:
            new_edges[perm[u]].append(perm[v])
    return new_edges


# XXX Test case generators for the individual functions.

def all_factors_generator(seed):
    for n in range(2, 1000):
        yield n,
    rng = Random(seed)
    n = 1000
    for _ in range(700):
        n += rng.randint(1, n // 50)
        yield n,


def levine_sequence_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(2, 13, 15), pyramid(2, 8, 12)), 100):
        items = [rng.randint(1, m) for _ in range(n)]
        k = rng.randint(1, 1 + m)
        yield items, k


def yellowstone_sequence_generator(seed):
    for n in range(10000):
        yield n,


def tanton_necklace_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(3, 4, 5), cycle([20, 30, 50, 70])), 2000):
        beads, pc, oc = [], 0, 0
        for _ in range(2 * n):
            b = rng.choice("po") if (not beads or rng.randint(0, 99) < p) else rng.choice(beads)
            if b == 'p' and pc == n:
                b = 'o'
            if b == 'o' and oc == n:
                b = 'p'
            beads.append(b)
            if b == 'p':
                pc += 1
            else:
                oc += 1
        yield "".join(beads), rng.randint(2, n - 1)


def equal_sum_partition_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(6, 4, 5), cycle([0, 2, 4])), 1500):
        items = []
        s = rng.randint(n, 2 * n)
        for _ in range(rng.randint(3, n)):
            block = []
            ss = s
            while ss > 0:
                e = isqrt(ss * ss - rng.randint(1, ss * ss)) + 1
                ss -= e
                block.append(e)
                if rng.randint(0, 100) < p:
                    block.append(rng.randint(1, 2 * ss + 2))
            rng.shuffle(block)
            items.extend(block)
        yield items,


def max_blocks_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(5, 2, 2), 4000):
        perm = list(range(n))
        rng.shuffle(perm)
        yield perm,


def lcsis_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(0, 2, 2), 200):
        k = (n + 3) ** 2
        seq = sorted(rng.sample(range(k), n), reverse=True)
        itemss = []
        for _ in range(2):
            m = rng.randint(n, 3 * n + 3)
            items, seqq = [], seq[:]
            while seqq:
                if rng.randint(0, 100) < 50:
                    items.append(seqq.pop())
                else:
                    items.append(rng.randint(0, m))
            itemss.append(items)
        yield itemss[0], itemss[1]


def liquid_sort_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 6, 8), 250):
        tubes = [[] for _ in range(rng.randint(n + 1, n + 2))]
        liquid = [m // 4 for m in range(4 * n)]
        rng.shuffle(liquid)
        for x in liquid:
            i = rng.randint(0, n - 1)
            while len(tubes[i]) == 4:
                i = (i + 1) % n
            tubes[i].append(x)
        yield tubes,


def mixed_sort_generator(seed):
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        word_list = [w.strip() for w in f if 4 < len(w) < 8]
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 1, 1), pyramid(10, 1, 1)), 1000):
        k = rng.randint(0, n)
        ints = [rng.randint(-m, m) for _ in range(k)]
        strs = rng.sample(word_list, n - k)
        items = ints + strs
        rng.shuffle(items)
        yield items,


def largest_rectangle_generator(seed):
    rng = Random(seed)
    for n, m, p in islice(zip(pyramid(2, 2, 2), pyramid(10, 1, 1), cycle([40, 60, 90])), 5000):
        h = rng.randint(1, m)
        height = [h]
        for _ in range(n):
            if rng.randint(0, 99) < p:
                h = abs(h + rng.randint(-3, 3))
            else:
                h = rng.randint(1, m)
            height.append(h)
        yield height,


def spiral_walk_generator(seed):
    rng = Random(seed)
    yield from [(1, 0, 0), (0, 1, 0), (1, 0, 1), (0, 1, 1), (-1, 0, 1), (0, -1, 1)]
    for n in chain(islice(pyramid(2, 2, 2), 500), islice(scale_random(100, 6, 5), 200)):
        m = isqrt(n) + 2
        dx = rng.randint(-m, m)
        dy = rng.randint(-m, m)
        yield dx, dy, n


def strahler_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 2, 2), 1000):
        flows = [[], [0]]
        for i in range(2, n):
            m = rng.randint(1, i - 1)
            flow = rng.sample(range(i), m)
            flows.append(flow)
        yield flows,


def random_walk_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(2, 4, 5), pyramid(5, 8, 10)), 500):
        a = rng.randint(1, m)
        b = rng.randint(a + 1, m + 1)
        left_p = F(a, b)
        a = rng.randint(1, m)
        b = rng.randint(a + 1, m + 1)
        right_p = (1 - left_p) * F(a, b)
        curr_p = 1 - left_p - right_p
        pos = rng.sample(range(-n, n + 1), isqrt(n))
        yield [left_p, curr_p, right_p], n, pos


def candy_split_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 2, 2), pyramid(2, 1, 1)), 1500):
        candies = [2 * rng.randint(0, m) for _ in range(n)]
        yield candies,


def car_match_generator(seed):
    rng = Random(seed)
    for n, m, p in islice(zip(pyramid(4, 6, 8), pyramid(5, 3, 4), cycle([50, 70, 90, 100])), 200):
        rows = [[] for _ in range(n)]
        colour, trucks = 0, []
        for t in range(m):
            if t % 3 == 0:
                colour = rng.choice(range(5))
            trucks.append(colour)
            for _ in range(3):
                rows[rng.choice(range(n))].append(colour if rng.randint(0, 100) < p else rng.choice(range(5)))
        rows = [row[::-1] for row in rows]
        yield rows, trucks


def goldbach_generator(seed):
    n, rng = 4, Random(seed)
    for m in islice(pyramid(40, 1, 1), 5000):
        yield n,
        n += 2 * rng.randint(1, m)


def is_prime_generator(seed):
    some_primes = [
            47, 61, 67, 79, 89, 97,
            179, 223, 317, 467, 569, 601, 727, 757, 787, 919, 929, 967,
            1289, 1451, 1721, 2887, 3001, 3697, 4339, 4517, 6353, 6719, 9511,
            18913, 20233, 31891, 34939, 43613, 51539, 65423, 73999, 78853, 78977, 80071, 89069,
            100517, 100703, 124769, 312383, 344249, 502703, 601319, 655211, 889951,
            1433477, 1984007, 2570651, 4322909, 4324601, 4325813, 5873227, 6000061, 6540407, 8214091, 9874693,
            10001713, 12914771, 14001989, 42324409, 54003253, 51001889, 72173327, 78298873, 88824301, 92323657,
            123126557, 133849141, 231232117, 236476577, 312136789, 374614003, 378298727, 432232223,
            588323209, 636474869, 636478343, 718398173, 812134459, 931233647, 932498947, 943235653,
            1234568837, 1534569727, 1999970333, 2071119119
    ]
    some_composites = [
            3613 * 4057, 65633 * 2713, 84223 * 569, 1013 * 6353, 655507 * 101, 3307 * 3307,
            67481 * 23, 4321787 * 53, 32969 * 62987, 1451 * 499 * 359, 44483 * 119, 971 * 191,
            1249 * 50951, 6907 * 6907, 30859 * 31883, 37649 * 7879, 56009 * 13, 147607 * 137,
            148301 * 593, 1171 * 1867, 7001 * 967, 544897 * 201, 1451 * 787, 727 * 757 * 787,
            565559 * 137, 239 * 613 * 349, 1069 * 157 * 71, 1985713 * 47, 276047 * 97, 45347263,
            45347769,
            # https://oeis.org/A014233, some Miller - Rabin pseudoprimes
            2047, 1373653, 25326001,
            # https: //oeis.org/A001567, some Fermat pseudoprimes
            341, 561, 645, 1105, 1387, 1729, 1905, 2047, 2465, 2701, 2821, 3277, 4033, 4369, 4371,
            4681, 5461, 6601, 7957, 8321, 8481, 8911, 10261, 10585, 11305, 12801, 13741, 13747,
            13981, 14491, 15709, 15841, 16705, 18705, 18721, 19951, 23001, 23377, 25761, 29341,
            2615977, 26634301, 69741001, 1693101241,
            # https: //oeis.org/A006972, some Lucas - Carmichael numbers
            399, 935, 2015, 2915, 4991, 5719, 7055, 8855, 12719, 18095, 20705, 20999, 22847, 29315,
            31535, 46079, 51359, 60059, 63503, 67199, 73535, 76751, 80189, 81719, 88559, 90287,
            104663, 117215, 120581, 147455, 152279, 155819, 162687, 191807, 194327, 196559, 214199,
            9868715, 11521439, 43383167, 126806399, 632309759, 1454412959,
            # https://oeis.org/A257750, some quasi - Carmichael numbers
            77, 143, 165, 187, 209, 221, 231, 247, 273, 299, 323, 357, 391, 399, 437, 493, 527,
            561, 589, 598, 713, 715, 899, 935, 943, 989, 1015, 1073, 1105, 1147, 1189, 1247, 1271,
            1295, 1333, 1517, 1537, 1547, 1591, 1595, 1705, 1729, 1739, 1763, 1829, 1885, 1886, 1927,
            63169, 198547, 500039, 3534541, 5971357, 9445027, 13989667,
            # https://oeis.org/A001262, some strong pseudoprimes, base 2
            2047, 3277, 4033, 4681, 8321, 15841, 29341, 42799, 49141, 52633, 65281, 74665, 80581,
            85489, 88357, 90751, 104653, 130561, 196093, 220729, 233017, 252601, 253241, 256999,
            271951, 280601, 314821, 357761, 390937, 458989, 476971, 486737, 3605429, 21417991,
            77812153, 82870517, 180497633, 327398009, 705351583, 1027744453,
            # https://oeis.org/A020229, some strong pseudoprimes, base 3
            121, 703, 1891, 3281, 8401, 8911, 10585, 12403, 16531, 18721, 19345, 23521, 31621, 44287,
            47197, 55969, 63139, 74593, 79003, 82513, 87913, 88573, 97567, 105163, 111361, 112141,
            148417, 152551, 182527, 188191, 211411, 218791, 221761, 226801, 2226043, 35728129,
            69444841, 117987841, 220534651, 378682537, 487890703, 1095485821,
            # https://oeis.org/A020231, some strong pseudoprimes, base 5
            781, 1541, 5461, 5611, 7813, 13021, 14981, 15751, 24211, 25351, 29539, 38081, 40501,
            44801, 53971, 79381, 100651, 102311, 104721, 112141, 121463, 133141, 141361, 146611,
            195313, 211951, 216457, 222301, 251521, 289081, 290629, 298271, 315121, 1197761,
            5481451, 27722857, 45006391, 75663451, 105957601, 528968917, 643767931, 1063398043
    ]
    for n in chain(some_primes, some_composites):
        yield n,


def knight_watch_generator(seed):
    rng = Random(seed)
    for n, k in islice(zip(pyramid(4, 6, 6), pyramid(2, 10, 11)), 300):
        m = rng.randint(n, 2 * n)
        tabu = rng.sample(list(product(range(n), repeat=2)), m)
        (sx, sy) = tabu.pop()
        yield n, sx, sy, k, tabu


def conway_subprime_generator(seed):
    rng = Random(seed)
    for b, n in islice(zip(count(2), pyramid(1, 2, 2)), 1000):
        for a in rng.sample(range(1, b + 1), n):
            yield a, b


def one_zero_generator(seed):
    for n in range(1, 2000):
        yield n,


def bug_in_a_line_generator(seed):
    for n in range(1, 5):
        for board in product('RYG', repeat=n):
            yield "".join(board),
    rng = Random(seed)
    for n in islice(pyramid(5, 3, 4), 3000):
        board = [rng.choice('RYG') for _ in range(n)]
        board[0] = rng.choice('YG')
        board[1] = rng.choice('YG')
        yield "".join(board),


def maximum_overlap_intervals_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 2), 2000):
        perm = list(range(0, 2 * n))
        rng.shuffle(perm)
        events = []
        for i in range(0, 2*n, 2):
            s, e = perm[i], perm[i + 1]
            events.append((min(s, e), max(s, e)))
        yield sorted(events),


def gladiators_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 10, 20), 250):
        gladiators = [rng.randint(1, n*n) for _ in range(2 * n)]
        yield gladiators[:n], gladiators[n:]


def maximum_interval_clique_generator(seed):
    rng = Random(seed)
    for n in chain(islice(pyramid(3, 2, 2), 500), range(1000, 1500)):
        perm = list(range(0, 2 * n))
        rng.shuffle(perm)
        events = []
        for i in range(0, 2*n, 2):
            s, e = perm[i], perm[i + 1]
            events.append((min(s, e), max(s, e)))
        yield sorted(events),


def vigenere_generator(seed):
    rng = Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        word_list = [w.strip() for w in f if 4 < len(w) < 8]
    for n in islice(pyramid(2, 5, 6), 1000):
        text = "".join(rng.sample(word_list, n))
        key = "".join(rng.sample(word_list, n // 2))
        yield text, key, +1
        yield text, key, -1


def farthest_points_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(6, 3, 4), pyramid(20, 1, 1)), 500):
        pos = sorted(rng.sample(range(p), n))
        k = rng.randint(3, max(4, n // 3))
        yield pos, p, k


def queue_jockeys_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(2, 4, 5), pyramid(4, 2, 3)), 500):
        perm = list(range(n))
        rng.shuffle(perm)
        moves = [rng.randint(0, n-1) for _ in range(m)]
        yield perm, moves

    def gen(n_, m_, s):
        rng2 = Random(s)
        for _ in range(m_):
            yield rng2.randint(0, n_ - 1)

    for n in range(1000, 1100):
        perm = list(range(n))
        rng.shuffle(perm)
        yield perm, gen(n, n * 20, seed + n)


def falling_squares_generator(seed):
    rng, s = Random(seed), 1
    for i, n in enumerate(islice(pyramid(3, 2, 2), 3000)):
        squares, m = [], 10
        if i > 300 and i % 10 == 0:
            s = 2 * s
        for _ in range(n):
            x = rng.randint(0, s * m)
            h = rng.randint(1, s * isqrt(m))
            m += 1
            squares.append((x, h))
        yield squares,


def knaves_of_round_table_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(3, 4, 5), cycle(range(20, 100, 20))), 3000):
        truth = [int(rng.randint(0, 100) < p) for _ in range(n)]
        answers = [None for _ in range(n)]
        for i in range(n):
            s = truth[(i+1) % n] + truth[(i-1) % n]
            if truth[i]:
                answers[i] = s
            else:
                v = rng.randint(0, 2)
                while v == s:
                    v = rng.randint(0, 2)
                answers[i] = v
        yield answers,
        

def albuquerque_stretch_generator(seed):
    yield "albuquerque",
    rng = Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        word_list = [w.strip() for w in f if 3 < len(w) < 7]
    for n in islice(pyramid(2, 4, 5), 1000):
        text = "".join(rng.sample(word_list, n))
        yield text,


def descending_suffix_game_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(5, 3, 3), pyramid(2, 4, 5)), 100):
        board = rng.sample(range(1, n+1), n - m)
        yield board, n


def maximal_confusion_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(5, 2, 2), cycle([30, 40, 50])), 5000):
        answers = [rng.choice("TF")]
        for _ in range(n):
            answers.append(answers[-1] if rng.randint(0, 99) < p else rng.choice("TF"))
        yield "".join(answers), rng.randint(2, max(n // 3, 3))


def approval_voting_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 10, 11), pyramid(5, 3, 4)), 1000):
        ballots = []
        for _ in range(m):
            ballot = "".join(rng.choice("YN") for _ in range(n))
            ballots.append(ballot)
        yield ballots,


def cyk_parser_generator(seed):
    rng = Random(seed)

    for n, m in islice(zip(pyramid(3, 5, 6), pyramid(3, 4, 4)), 500):
        nonterm, term, rules_set = ups[:n], lows[:m], set()
        for c in term:
            for d in rng.sample(nonterm, rng.randint(1, max(2, n - 3))):
                rules_set.add((d, c))
        for d in nonterm:
            for _ in range(rng.randint(1, 3)):
                rh1 = rng.choice(nonterm)
                rh2 = rng.choice(nonterm)
                rules_set.add((d, rh1 + rh2))
        rules = {d:[] for d in nonterm}
        for (d, rhs) in rules_set:
            rules[d].append(rhs)

        text = "".join(rng.choice(term) for _ in range(m))
        yield text, rules


def rational_roots_generator(seed):
    for coeff in [(-4, -5, -5, -1), (9, -7, -2), (-8, 10), (9, -4), (-8, -6, -1), (5, -7), (9, -5),
                  (-2, 8), (3, 4), (1, -4, 7, -2, -3, -8, -4), (-6, -6, 6, -4, -2, -4, -2, 1, -9), (-6, -3),
                  (-10, -5, -6, 6, 6, -6, 5), (1, -8), (1, 0, -4), (3, -6), (2, -2), (3, -6), (7, -1),
                  (1, 4), (4, 8, 4), (-10, 1), (10, -2), (4, 8), (1, 2), (8, 8), (-3, -6), (-8, 2, -2, -2, 3),
                  (-1, 2), (-1, -2), (-4, -9), (2, 8), (1, -5), (-2, -8), (-1, -2), (-7, 8, -1), (6, -7, -3, 1),
                  (4, -7, 5, 5, -7, 7, 3), (3, -3), (6, -5), (5, -8), (9, -10), (-6, 5), (-1, -1, -2, -5, -3, -1, 7, 8),
                  (-10, 7, 2, -8), (-8, 8), (-10, -3), (-1, -3), (-4, -3), (-6, 4, 5, -5, -5, -4, -1, -2),
                  (1, -7), (6, 7, -9, 9, 6, 5, 6, -1, 3, -8), (-8, 2, 1), (5, -13, 1, 2), (-252, 10756, -64383, 4544),
                  (210, -47, -4, 1), (18, -27, 1, 4), (24, -14, -13, 2, 1), (6, 13, -116, -143, 60),
                  (-70, 73, 8), (100, 20, 1), (-100, 0, 1), (2, 87, -180, 91), (-2, -1, 24642, 12321),
                  (60, 148, 103, -2, -20, -2, 1), (-360, 531, 7309, -8130, -25000, -5856, 3456), (-4158, 57, 4300),
                  (-15, 163, 2002), (728, 2658, -22225, -1335, 4262, 792)]:
        yield coeff,
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 3, 3), pyramid(11, 2, 2)), 5000):
        coeff = [rng.randint(-10, 10) for _ in range(rng.randint(1, 10))]
        while coeff[0] == 0:
            coeff[0] = rng.randint(-10, 10)
        while coeff[-1] == 0:
            coeff[-1] = rng.randint(-10, 10)
        yield tuple(coeff),


def sublist_sum_k_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 1, 1), 10000):
        items = [rng.randint(1, n * n) for _ in range(n)]
        s = sum(items)
        if rng.randint(0, 99) < 20:
            k = rng.randint(s // 8, 3 * s // 8)
        else:
            i = rng.randint(0, n - 2)
            j = rng.randint(i + 1, n - 1)
            k = sum(items[i:j]) + rng.choice([0, 0, 0, 1])
            if k > 200 and rng.randint(0, 99) < 50:
                k = k // rng.choice([2, 3, 5, 7, 11])
        yield items, k


def max_three_disjoint_sublists_generator(seed):
    for items in [[2, 3, 4, -5, -5, -5], [-2, -4, -5, 1, 2, 3], [-2, -2, -2]]:
        yield items,
    rng = Random(seed)
    for n in islice(pyramid(5, 1, 1), 1000):
        items = []
        for _ in range(n):
            items.append(rng.randint(-n, -1) if rng.randint(0, 99) < 60 else rng.randint(1, 2*n))
        yield items,


def optimal_bridges_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(5, 1, 1), 200):
        nn = isqrt(n)
        perm = list(range(n))
        rng.shuffle(perm)
        yield perm, rng.randint(nn, max(n // 3, nn + 1))


def expand_string_generator(seed):
    rng = Random(seed)
    alphabet = 'abcdefghijklmnopqrstuvwxyz'

    def build(d, m):
        if d < 1:
            result = rng.choice(alphabet)
            while rng.randint(0, 99) < 40:
                result += rng.choice(alphabet)
            return result
        else:
            result = ""
            for _ in range(rng.randint(1, m)):
                piece = build(rng.randint(0, d - 1), max(d - 1, m - 1))
                result += piece if rng.randint(0, 99) < 50 else f"{rng.randint(2, m)}[{piece}]"
            return result

    for n, m in islice(zip(pyramid(2, 21, 30), pyramid(4, 17, 25)), 700):
        yield build(n, m),


def first_singleton_generator(seed):
    rng = Random(seed)
    alphabet = 'abcdefghijklmnopqrstuvwxyz'
    for n, p in islice(zip(pyramid(4, 1, 1), cycle([20, 50, 80])), 3000):
        alpha = rng.sample(alphabet, rng.randint(6, 25))
        singles = rng.sample(alpha, rng.randint(3, 5))
        doubles = [c for c in alpha if c not in singles]
        text = rng.choice(alpha)
        for _ in range(n):
            if len(text) > 3 and rng.randint(0, 99) < p:
                text += rng.choice(text)
            else:
                if len(singles) > 0 and rng.randint(0, 99) < 30:
                    c = rng.choice(singles)
                    singles = [d for d in singles if d != c]
                    text += c
                else:
                    text += rng.choice(doubles)
        yield text,


def tarjans_scc_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(5, 2, 2), cycle([20, 40, 60])), 2000):
        remain, comps, edge_set = list(range(n)), [], set()
        # Create each SCC
        while len(remain) > 0:
            comp = rng.sample(remain, rng.randint(1, len(remain)))
            if len(comp) > 1:
                for i in range(0, len(comp)):
                    edge_set.add((comp[i], comp[(i+1) % len(comp)]))
            comps.append(comp)
            remain = [u for u in remain if u not in comp]
        # Create more random edges
        for _ in range(rng.randint(n, 2*n)):
            i = rng.randint(0, len(comps) - 1)
            j = rng.randint(i, len(comps) - 1)
            u = rng.choice(comps[i])
            v = rng.choice(comps[j])
            edge_set.add((v, u))
        # Convert edges to edge list and yield
        edges = [[] for _ in range(n)]
        for (u, v) in edge_set:
            edges[u].append(v)
        yield edges,


def toads_and_frogs_generator(seed):
    for board in ["T.F", "T..F", "TT.FF", "T..FT..F"]:
        yield board,
    rng = Random(seed)
    for n, m, pp in islice(zip(pyramid(8, 2, 3), pyramid(2, 10, 12), cycle([20, 40, 60])), 150):
        pos = sorted(rng.sample(range(n), 2*m))
        while rng.randint(0, 100) < pp:
            i = rng.randint(1, m - 1)
            j = rng.randint(m, 2*m - 2)
            pos[i], pos[j] = pos[j], pos[i]
        board = ["." for _ in range(n)]
        for p in pos[:m]:
            board[p] = 'T'
        for p in pos[m:]:
            board[p] = 'F'
        yield "".join(board),


def burrows_wheeler_encode_generator(seed):
    rng = Random(seed)
    for text in ["a$", "aa$", "abc$", "abab$", "baba$", "baab$"]:
        yield text, range(len(text))
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        word_list = [w.strip() for w in f if 6 < len(w)]
    for n in range(3, 500):
        words = rng.sample(word_list, n)
        words.append("$")
        words = "".join(words)
        positions = sorted(rng.sample(range(len(words)), rng.randint(3, 7)))
        yield words, positions


def maximal_repeats_generator(seed):
    rng = Random(seed)
    for n, m, k in islice(zip(pyramid(10, 2, 2), cycle(range(2, 9)), cycle(range(2, 6))), 2000):
        text, alpha = "", "abcdefgh"[:m]
        while len(text) < n:
            if len(text) < 2 or rng.randint(0, 99) < 40:
                text += rng.choice(alpha)
            else:
                i = rng.randint(0, len(text) - 2)
                j = rng.randint(i + 1, len(text))
                text += text[i:j]
        yield text, k


def min_max_triangle_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 2, 3), 100):
        points = set()
        while len(points) < 3*n:
            x = rng.randint(0, n*n)
            y = rng.randint(0, n*n)
            points.add((x, y))
        yield list(points),


def shell_sort_generator(seed):
    mersenne = [1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383]
    pow2_plus1 = [1, 3, 5, 9, 17, 33, 65, 129, 257, 513, 1025, 2049, 4097, 8193, 16385]
    hamming = [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36, 48, 54, 64, 72, 81, 96,
               108, 128, 144, 162, 192, 216, 243, 256, 288, 324, 384, 432, 486, 512, 576,
               648, 729, 768, 864, 972, 1024, 1152, 1296, 1458, 1536, 1728, 1944, 2048,
               2187, 2304, 2592, 2916, 3072, 3456, 3888]
    ciura = [1, 8, 23, 77, 281, 1073, 4193]
    lee_tokuda = [1, 4, 9, 20, 45, 102, 230, 516, 1158, 2599]
    gapss = [mersenne, pow2_plus1, hamming, ciura, lee_tokuda]
    for n in range(1, 6):
        for p in permutations(range(n)):
            yield list(p), [g for g in ciura if g < n]
    rng = Random(seed)
    for n, gaps in zip(range(6, 2000), cycle(gapss)):
        perm = list(range(n))
        rng.shuffle(perm)
        yield perm, [g for g in gaps if g < n]


def from_simple_continued_fraction_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(2, 2, 3), pyramid(7, 3, 4)), 2000):
        yield [rng.randint(1, m) for _ in range(n)],


def to_simple_continued_fraction_generator(seed):
    for (a, b) in combinations(__primes, 2):
        yield a, b
    for (a, b, c) in combinations(__primes, 3):
        yield a, b * c
        yield (c, a * b) if a * b > c else (a * b, c)
    rng = Random(seed)
    for n in islice(scale_random(seed, 2, 5), 500):
        yield rng.randint(1, n -1), n


def instant_runoff_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 6, 7), pyramid(5, 4, 4)), 2000):
        ballots = []
        ballot = list(range(n))
        for _ in range(m):
            if rng.randint(0, 99) < 30:
                rng.shuffle(ballot)
            else:
                i = rng.randint(1, n - 1)
                ballot[0], ballot[i] = ballot[i], ballot[0]
            ballots.append(ballot[:])
        yield ballots,


def fox_and_hounds_generator(seed):
    rng = Random(seed)
    for _ in range(100):
        pos = set()
        while len(pos) < 5:
            row = rng.randint(0, 7)
            col = rng.randint(0, 7)
            if row % 2 != col % 2:
                pos.add((row, col))
        pos = sorted(pos)
        yield pos[4], pos[:4],


def merge_biggest_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 1, 1), 10000):
        yield [rng.randint(1, 3*n) for _ in range(n)],


def maximum_word_select_generator(seed):
    rng = Random(seed)
    alphabet = 'abcdefghijklmnopqrstuvwxyz'
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        word_list = [w.strip() for w in f if 3 <= len(w) <= 8 or rng.randint(0, 99) < 10]
    for n in islice(pyramid(4, 2, 2), 120):
        words = rng.sample(word_list, n)
        letters = [c if rng.randint(0, 99) < 85 else rng.choice(alphabet) for c in "".join(words)]
        yield words, "".join(sorted(letters))


def generalized_fibonacci_generator(seed):
    for n in range(3, 20):
        yield (1, 1), n      # Fibonacci
        yield (1, 1, 1), n   # Tribonacci
        yield (1, 2), n      # Pell
        yield (2, 1), n      # Jacobstahl
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 5, 6), pyramid(20, 1, 1)), 1000):
        multipliers = tuple(rng.randint(-n, n) for _ in range(n))
        k = rng.randint(n+1, m)
        yield multipliers, m


def sultans_daughter_generator(seed):
    rng = Random(seed)
    for digits in ["663653", "140952", "111122", "1171112222", "61111679612222",
                   "1113151722222", "161316111267647653667222222", "13115616633131152222222",
                   "47536414753642", "47431474312", "4447431474312", "5647431474312"]:
        yield digits,

    def create(depth):
        if depth < 1:
            tail = create(depth) if rng.randint(0, 99) < 50 else ""
            return rng.choice("0123456789") + tail
        else:
            y = create(depth - 1)
            roll = rng.randint(0, 99)
            if roll < 30:
                return "1" + y + "2"
            elif roll < 45:
                return "3" + y
            elif roll < 60:
                return "4" + y
            elif roll < 70:
                return "5" + y
            elif roll < 80:
                return "6" + y
            elif roll < 90:
                return "7" + y
            else:
                return rng.choice("89") + y

    for n in islice(pyramid(3, 3, 2), 500):
        yield create(n),


def partition_point_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(4, 1, 1), 10000):
        k = rng.randint(1, n - 1)
        items = [rng.randint(0, n*n) for _ in range(k)]
        m = max(items)
        items.extend(rng.randint(m + 1, 2 * m) for _ in range(n - k + 1))
        yield items,


def sturm_word_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(20, 1, 1), 1000):
        x = rng.randint(1, n)
        y = rng.randint(x + 1, 2 * n)
        g = gcd(x, y)
        x, y = x // g, y // g
        yield x, y
        yield y, x


def double_ended_pop_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(10, 1, 1), pyramid(20, 4, 5)), 3000):
        items = [rng.randint(0, m) for _ in range(n)]
        k = rng.randint(4, n // 2)
        yield items, k


def palindrome_split_generator(seed):
    for text in ["X", "AA", "AAA", "ABA", "ABBA", "ABAB", "ABACAB"]:
        yield text,
    rng = Random(seed)
    for n, m in islice(zip(pyramid(4, 1, 1), pyramid(3, 10, 10)), 1000):
        alpha = ups[:rng.randint(2, m)]
        text = rng.choice(alpha)
        while len(text) < n:
            c = rng.randint(0, 99)
            if len(text) < 4 or c < 30:
                text += rng.choice(alpha)
            elif c < 60:
                k = rng.randint(2, len(text))
                text += text[:-k:-1]
            else:
                k1, k2 = rng.sample(range(len(text)), 2)
                k1, k2 = min(k1, k2), max(k1, k2)
                text += text[k1:k2]
        yield text,


def assign_sides_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 2, 2), pyramid(6, 1, 1)), 1000):
        costs = []
        for _ in range(2 * n):
            a = rng.randint(1, m)
            b = rng.randint(1, m)
            costs.append((a, b))
        yield costs,


def colonel_blotto_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 3, 4), 2500):
        prize = [rng.randint(1, 3*n) for _ in range(n)]
        values = sorted(range(n), key=lambda i:(-prize[i], i))
        units = [rng.randint(1, 10) for _ in range(2*n)]
        units.sort(reverse=True)
        enemy = [2*u + 1 for u in units[0::2]]
        enemy = [enemy[values[i]] for i in range(n)]
        for _ in range(rng.randint(0, min(n, 4))):
            i = rng.randint(0, n-1)
            j = rng.randint(0, n-1)
            enemy[i], enemy[j] = enemy[j], enemy[i]
        friend = [2*u for u in units[1::2]]
        yield friend, enemy, prize


def maximal_cliques_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(6, 2, 3), cycle([10, 40, 60])), 1000):
        edge_set = set()
        nn = (n * (n - 1)) // 6
        m = rng.randint(nn, 2*nn)
        while len(edge_set) < m:
            k = 2
            while k < n - 2 and rng.randint(0, 99) < p:
                k += 1
            nodes = rng.sample(range(n), k)
            for u, v in combinations(nodes, 2):
                edge_set.add(((min(u, v), max(u, v))))
        edges = [[] for _ in range(n)]
        for (u, v) in edge_set:
            edges[u].append(v)
            edges[v].append(u)
        yield edges,


def chunk_sorting_generator(seed):
    rng = Random(seed)
    for n in range(1, 4):
        for perm in permutations(range(n)):
            yield list(perm),
    for n in islice(pyramid(4, 1, 3), 20000):
        perm, prev = [], 0
        items = rng.sample(range(1, n), rng.randint(0, n - 3))
        items.append(n)
        items.sort()
        for c in items:
            chunk = list(range(prev, c))
            rng.shuffle(chunk)
            perm.extend(chunk)
            prev = c
        yield perm,


def bays_durham_shuffle_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(10, 2, 2), pyramid(10, 1, 1)), 5000):
        k = rng.randint(3, n // 2)
        yield (rng.randint(0, m) for _ in range(n)), k


def maximum_repeated_suffix_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(2, 1, 1), pyramid(3, 10, 12)), 10000):
        items = []
        while len(items) < n:
            if len(items) < 3 or rng.randint(0, 99) < 50:
                items.append(rng.randint(0, m))
            else:
                i = rng.randint(0, len(items) - 2)
                j = rng.randint(i, len(items))
                items += items[i:j]
        if rng.randint(0, 100) < 90:
            i = rng.randint(0, len(items) - 2)
            items += items[i:]
        yield items,


def count_slices_with_sum_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 1, 1), pyramid(2, 7, 12)), 5000):
        items = [rng.randint(1, m)]
        while len(items) < n:
            if len(items) < 4 or rng.randint(0, 99) < 50:
                items.append(rng.randint(1, m))
            else:
                i = rng.randint(0, len(items) - 2)
                j = rng.randint(i + 1, len(items))
                items.extend(items[i::j])
        i = rng.randint(0, n - 2)
        j = rng.randint(i + 1, n)
        yield items, sum(items[i:j])


def count_increasing_paths_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 2, 2), 500):
        v = list(range(n*n))
        rng.shuffle(v)
        matrix = [v[i:i+n] for i in range(0, n*n, n)]
        yield matrix


def slater_velez_generator(seed):
    for n in range(2, 5000):
        yield n,


def diamond_sequence_generator(seed):
    for n in range(2, 100000):
        yield n,


def multiple_winner_election_generator(seed):
    yield [128, 115, 26, 23], 21, "dhondt"
    yield [128, 115, 26, 23], 21, "webster"
    yield [128, 115, 26, 23], 21, "imperiali"
    rng = Random(seed)
    for n, m in islice(zip(pyramid(2, 3, 5), pyramid(4, 2, 1)), 500):
        v = rng.randint(n*m, 2*n*m)
        votes = [rng.randint(2, 3 + v // 10) for _ in range(n)]
        while v > 0:
            i = rng.randint(0, n - 1)
            vv = rng.randint(min(3, v), max(4, v//10))
            votes[i] += vv
            v -= vv
        votes.sort(reverse=True)
        seats = rng.randint(m, 3*m)
        yield votes, seats, "dhondt"
        yield votes, seats, "webster"
        yield votes, seats, "imperiali"


def pebblery_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(4, 2, 2), 120):
        pred = [[] for _ in range(n)]
        for i in range(1, n):
            pred[rng.randint(0, i-1)].append(i)
            for _ in range(rng.randint(0, 3)):
                j = rng.randint(0, i - 1)
                if i not in pred[j]:
                    pred[j].append(i)
        yield pred,


def poker_test_generator(seed):
    yield [1, 2, 3, 4 ,5],
    rng = Random(seed)
    for n, m, p in islice(zip(pyramid(10, 1, 1), pyramid(5, 6, 7), cycle([0, 40, 70])), 3000):
        seq = [rng.randint(0, m)]
        for _ in range(n):
            if rng.randint(0, 99) < p and len(seq) > 2:
                seq.append(seq[rng.randint(-3, -1)])
            else:
                seq.append(rng.randint(0, m))
        yield seq,


def is_semiconnected_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(4, 2, 2), 800):
        edge_set = set()
        m = rng.randint(n, (n*n)//3)
        while len(edge_set) < m:
            u = rng.randint(0, n-1)
            v = rng.randint(0, n-1)
            if u != v:
                edge_set.add((u, v))
        edges = [[] for _ in range(n)]
        for (u, v) in edge_set:
            edges[u].append(v)
        yield edges,


def post_correspondence_problem_generator(seed):
    yield ["a", 'ab', 'bba'], ['baa', 'aa', 'bb'], 5, 20
    yield ["aa", "b"], ["a", "ab"], 2, 4
    rng = Random(seed)
    pieces = []
    for n in range(1, 5):
        for piece in product('ab', repeat=n):
            pieces.append("".join(piece))
    for n, m in islice(zip(pyramid(3, 5, 6), pyramid(4, 3, 4)), 500):
        sample = rng.sample(pieces, 2*n)
        prefix, postfix, top_longer, bottom_longer = False, False, False, False
        first, second = sample[:n], sample[n:]
        for (a, b) in zip(first, second):
            prefix = prefix or a.startswith(b) or b.startswith(a)
            postfix = postfix or a.endswith(b) or b.endswith(a)
            top_longer = top_longer or len(a) > len(b)
            bottom_longer = bottom_longer or len(a) < len(b)
        if prefix and postfix and top_longer and bottom_longer:
            yield first, second, m, rng.randint(m, 3*m),


def zeckendorf_decode_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 5, 8), pyramid(5, 2, 2)), 5000):
        fits = ""
        for _ in range(rng.randint(1, n)):
            prev = 0
            for _ in range(rng.randint(1, m)):
                curr = 0 if prev == 1 else rng.randint(0, 1)
                fits += str(curr)
                prev = curr
            fits += "11" if prev == 0 else "1"
        yield fits,


def average_run_length_generator(seed):
    for items in [[2, 2], [4, 4, 4, 1], [3, 3, 3, 3, 2, 5], [1, 2, 1, 0], [4, 3, 1], [1, 2, 1, 2, 1, 2]]:
        yield items,
    rng = Random(seed)
    for n, m, p in islice(zip(pyramid(2, 2, 2), pyramid(3, 8, 10), cycle([20, 30, 50])), 5000):
        items, d = [rng.randint(0, m)], rng.choice([-1, 1])
        while len(items) < n:
            items.append(abs(items[-1] + d * rng.randint(0, m)))
            if rng.randint(0, 99) < p:
                d = -d
        yield items,


def front_back_sort_generator(seed):
    for n in range(1, 10):
        for perm in permutations(range(n)):
            yield list(perm),


def pick_it_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 2, 3), pyramid(5, 3, 4)), 100):
        items = [rng.randint(1, m) for _ in range(n)]
        yield items,


def find_all_words_generator(seed):
    rng = Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [w.strip() for w in f if len(w) >= 8]
    for n in islice(pyramid(8, 6, 7), 200):
        letters = rng.choice(words)
        while len(letters) < n:
            letters += rng.choice(lows)
        letters = "".join(sorted([c for c in letters]))
        yield letters, words


def optimal_ab_filling_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 3), 1000):
        text = "".join(rng.choice("aabb...") for _ in range(n))
        ab = rng.randint(1, 5)
        ba = rng.randint(1, 5)
        yield text, ab, ba


def haircut_generator(seed):
    rng = Random(seed)
    for p, m in islice(zip(count(10), pyramid(3, 5, 6)), 500):
        speed = [rng.randint(10, 60) for _ in range(m)]
        n = rng.randint(5, p)
        yield speed, n


def bayes_dice_update_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(2, 4, 5), pyramid(10, 4, 6)), 200):
        dice = rng.sample(range(2, m + 1), n)
        dice.sort()
        d = rng.choice(dice)
        rolls = [rng.randint(1, d) for _ in range(1, n)]
        yield dice, rolls


def limited_swaps_generator(seed):
    rng = Random(seed)
    prev_n = 0
    for n in islice(pyramid(3, 5, 6), 200):
        if n != prev_n:
            pairs = list(combinations(range(n), 2))
        perm = list(range(n))
        rng.shuffle(perm)
        m = min(rng.randint(n//2, max(n + 2, (n * n - n - 3)//2)), len(pairs) - 1)
        swaps = rng.sample(pairs, m)
        swaps.sort()
        yield perm, swaps


def s_eval_generator(seed):
    rng = Random(seed)

    def create_expr(d, n):
        if d < 1:
            return rng.randint(0, 10**n)
        op = rng.choice("+-*")
        e1 = create_expr(rng.randint(0, d - 1), n)
        e2 = create_expr(rng.randint(0, d - 1), n)
        return f"({op} {e1} {e2})"

    yield "42"
    for d, n in islice(zip(pyramid(1, 3, 4), pyramid(1, 20, 30)), 1000):
        yield create_expr(d, n),


def odds_and_evens_generator(seed):
    yield from [('11', '1111'), ('10', '01'), ('0', '0000'), ('1111', '1'), ('000111', '111000') ]
    rng = Random(seed)
    for n in islice(pyramid(3, 3, 3), 300):
        first = random_string('01', n, rng)
        second = random_string('01', rng.randint(1, n), rng)
        yield (first, second) if rng.randint(0, 99) < 50 else (second, first)


def cousin_explainer_generator(seed):
    rng = Random(seed)
    for m, p in islice(zip(pyramid(6, 3, 0), pyramid(4, 20, 15)), 5000):
        a = rng.randint(1, m)
        b, steps1 = a, rng.randint(0, p)
        steps = steps1
        while b > 1 and steps1 > 0:
            b = b // 2
            steps1 -= 1
        steps2 = rng.randint(1, p + 2)
        while b < 2**11 and steps2 > 0:
            b = 2 * b + rng.randint(0, 1)
            steps2 -= 1
        if a != b:
            yield a, b
            if steps < 2:
                yield b, a


def lehmer_decode_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 3, 3), 3000):
        inv = [rng.randint(0, n - i) for i in range(n)]
        yield inv,


def lehmer_encode_generator(seed):
    rng = Random(seed)
    for n in range(1, 6):
        for p in permutations(range(n)):
            yield list(p),
    p = list(range(7))
    for n in islice(pyramid(7, 2, 2), 2000):
        if len(p) < n:
            p.append(n - 1)
        rng.shuffle(p)
        yield p[:],


def loopless_walk_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(2, 1, 1), cycle([20, 50, 70])), 4000):
        steps = []
        for _ in range(n):
            if len(steps) > 0 and rng.randint(0, 99) < p:
                steps.append(rng.choice(steps))
            else:
                steps.append(rng.choice(lows))
        yield "".join(steps)


def square_root_sum_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 2), 2000):
        n1, n2, d = [], [], rng.randint(0, 1)
        for _ in range(n):
            p = rng.randint(2, 3 * n) if n1 == [] else max(n1[-1], n2[-1])
            p1 = rng.randint(p + 1, p + 4)
            p2 = p1 + 1
            if d == 0:
                n1.append(p1)
                n2.append(p2)
            else:
                n1.append(p2)
                n2.append(p1)
            d = 1 - d
        yield n1, n2


def friendship_paradox_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(3, 2, 2), cycle([30, 50, 80])), 2000):
        friend_set = set()
        for i in range(0, n):
            friends = set()
            while len(friends) < 1 or rng.randint(0, 99) < p:
                j = rng.randint(0, n - 1)
                if i != j:
                    friends.add((i, j))
            for (i, j) in friends:
                friend_set.add((i, j))
                friend_set.add((j, i))
        friends = [[] for _ in range(n)]
        for (i, j) in friend_set:
            friends[i].append(j)
        yield friends,


def factoradic_base_generator(seed):
    for n in range(1, 100):
        yield n,
    for n in islice(scale_random(seed, 3, 4), 1500):
        yield n,


def tchuka_ruma_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 5, 6), 150):
        board = [0 for _ in range(n)]
        for i in range(1, n):
            board[i] = rng.randint(0, n)
        yield board,


def gauss_circle_generator(seed):
    for r in range(1, 2001):
        yield r,


def maximum_palindrome_generator(seed):
    for digits in ['0', '00', '123', '98', '123123123', '225588770099']:
        yield digits,
    rng = Random(seed)
    for n, p in islice(zip(pyramid(2, 2, 2), cycle([10, 50, 90])), 3000):
        digits = []
        for d in range(10):
            if rng.randint(0, 100) < 40:
                m = rng.randint(2, n//2 + 3)
                if rng.randint(0, 99) < p and m % 2 == 1:
                    m += 1
                digits.extend(str(d) for _ in range(m))
        if digits:
            rng.shuffle(digits)
            yield "".join(digits),


def ants_on_the_rod_generator(seed):
    yield [[1, 1], [2, 1], [3, 1], [4, -1]], 5
    rng = Random(seed)
    for n in islice(pyramid(2, 2, 3), 3000):
        w = rng.randint(2 * n, 3 * n)
        ants = [[pos, rng.choice([-1, +1])] for pos in sorted(rng.sample(range(1, w), n))]
        yield ants, w


def split_at_none_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(3, 2, 2), cycle([10, 30, 50])), 4000):
        items = [None if rng.randint(0, 99) < p else rng.randint(-3*n, 3*n) for _ in range(n)]
        yield items,


def multiply_and_sort_generator(seed):
    rng = Random(seed)
    for n in range(2, 4000):
        for mul in rng.sample(range(2, 13), 3):
            yield n, mul


def magic_knight_generator(seed):
    rng = Random(seed)
    for n in range(5, 300):
        if n % 2 != 0 and n % 3 != 0:
            items = sorted(rng.sample(range(1, n * n), 5))
            items.append(n * n)
            yield n, items


def power_prefix_generator(seed):
    rng = Random(seed)
    p = 1024
    for n in islice(pyramid(6, 2, 3), 300):
        power = str(p)
        prefix = power[:rng.randint(4, min(len(power), n))]
        prefix = "".join(d if rng.randint(0, 100) < 70 else '*' for d in prefix)
        yield prefix,
        p = p * (2 ** rng.randint(2, n))


def pinch_moves_generator(seed):
    yield ".BWW.WB", 'B'
    yield "RBW.BW", 'W'
    rng = Random(seed)
    for n in islice(pyramid(8, 10, 10), 500):
        board = ""
        captured = False
        player = rng.choice('BW')
        other = 'W' if player == 'B' else 'B'
        prev = rng.choice("BW")
        while len(board) < n:
            move = rng.randint(0, 100)
            if move < 20 and not captured:
                o1 = rng.randint(1, 3)
                o2 = rng.randint(1, 3)
                if rng.randint(0, 100) < 70:
                    board += f"{other * o1}{'R' * rng.randint(1, 2)}{other * o2}"
                else:
                    board += f"{other * o1}{'R' * rng.randint(1, 2)}{other}{'R' * rng.randint(1, 2)}{other * o2}"
                captured = True
            elif move < 50:
                board += '.'
            elif move < 80:
                board += f".{prev * rng.randint(1, 2)}"
                prev = 'B' if prev == 'W' else 'W'
            else:
                p = rng.randint(0, 2)
                o = rng.randint(0, 2)
                board += f".{player * p}{other * o}" if rng.randint(0, 100) < 50 else f".{other * o}{player * p}"
        yield board, player


def tom_and_jerry_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(6, 5, 8), 1500):
        edge_set = set()
        for u in range(1, n + 1):
            for _ in range(rng.randint(1, 3)):
                v = rng.randint(max(0, u - n//4), u - 1)
                edge_set.add((u, v))
        edges = [[] for _ in range(n + 1)]
        for (u, v) in edge_set:
            edges[u].append(v)
            edges[v].append(u)
        for u in range(1, n):
            if all(v < u for v in edges[u]):
                v = rng.randint(u + 1, n)
                edges[u].append(v)
                edges[v].append(u)
        yield n, edges


def cubes_on_trailer_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 15, 8), 60):
        xs = n
        ys = rng.randint(n, n + 2)
        zs = rng.randint(2, n + 1)
        xy = [[False for _ in range(ys)] for _ in range(xs)]
        xz = [[False for _ in range(zs)] for _ in range(xs)]
        yz = [[False for _ in range(zs)] for _ in range(ys)]
        for x in range(xs):
            for y in range(ys):
                z = rng.randint(1, zs) if rng.randint(0, 99) < 50 else 0
                if z > 0:
                    xy[x][y] = True
                    for zz in range(z):
                        xz[x][zz] = True
                        yz[y][zz] = True
        yield xy, xz, yz,


def powertrain_generator(seed):
    rng = Random(seed)
    for m in islice(pyramid(2, 4, 5), 5000):
        n = int(random_string("123456789", m, rng))
        if n != 2592:
            yield n,


def complex_base_decode_generator(seed):
    # All bit strings up to length 8
    yield "0",
    yield "1",
    for n in range(1, 8):
        for bits in product([0, 1], repeat=n):
            yield "1" + "".join(str(b) for b in bits),
    # The rest with fuzzing
    rng = Random(seed)
    for n in range(8, 2000):
        yield "1" + "".join(str(rng.randint(0, 1)) for _ in range(n)),


def set_splitting_generator(seed):
    rng = Random(seed)
    for n, w in islice(zip(pyramid(6, 10, 12), pyramid(3, 11, 12)), 2000):
        subsets = []
        m = rng.randint(n, 2 * n)
        while len(subsets) < m:
            k = rng.randint(2, w) if rng.randint(0, 99) < 60 else 2
            subset = sorted(rng.sample(range(n), k))
            if subset not in subsets:
                subsets.append(subset)
        yield n, subsets


def bandwidth_generator(seed):
    yield from islice(__graph_generator(Random(seed)), 70)


def manimix_generator(seed):
    for expr in ["[1]", "(2)", "[45]", "[54]", "(19)", "(123456)", "(90)", "[(13)2]", "([13]2)", "[(45)(27)]"]:
        yield expr,

    rng = Random(seed)

    def expr(d, m):
        if d == 0:
            return rng.choice("0123456789")
        else:
            inner = "".join([expr(rng.randint(0, d - 1), m) for _ in range(rng.randint(2, m))])
            return f"[{inner}]" if rng.randint(0, 99) < 50 else f"({inner})"

    for d, m in islice(zip(pyramid(3, 7, 9), pyramid(3, 6, 8)), 200):
        yield expr(d, m),


def accumulating_merge_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(4, 3, 3), 3000):
        items1 = [rng.randint(1, 3*n) for _ in range(rng.randint(1, n))]
        items2 = [rng.randint(1, 3*n) for _ in range(rng.randint(1, n))]
        yield items1, items2


def string_stretching_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(3, 4, 5), cycle([20, 40, 60])), 500):
        m = rng.randint(2, n)
        pattern = rng.choice(lows[:n+1])
        repeats = 0
        for _ in range(m - 1):
            if repeats < 3  and rng.randint(0, 99) < p:
                repeats += 1
                pattern += rng.choice(pattern)
            else:
                pattern += rng.choice(lows[:n+1])
        text = pattern
        for _ in range(rng.randint(1, (n//2) + 1)):
            i = rng.randint(0, len(text))
            text = text[:i] + pattern + text[i:]
        yield text,


def conway_coin_race_generator(seed):
    rng = Random(seed)
    # Try out explicitly all patterns up to length 4
    for n in range(1, 5):
        for a in product([0, 1], repeat=n):
            a = "".join(str(bit) for bit in a)
            for b in product([0, 1], repeat=n):
                b = "".join(str(bit) for bit in b)
                if a < b:
                    yield a, b
    # Rest with fuzzing
    for n in islice(pyramid(5, 3, 3), 2000):
        a = "".join([rng.choice(["0", "1"]) for _ in range(n)])
        m = rng.randint(3, n)
        b = "".join([rng.choice(["0", "1"]) for _ in range(m)])
        if b not in a:
            yield a, b


def baker_norine_dollar_game_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(4, 2, 3), 150):
        edge_set = set()
        for u in range(1, n):
            v = rng.randint(0, u - 1)
            edge_set.add((u, v))
            edge_set.add((v, u))
        m = rng.randint(n, (n*(n-1))//3)
        while len(edge_set) < 2 * m:
            u = rng.randint(0, n - 1)
            v = rng.randint(0, n - 1)
            if u != v:
                edge_set.add((u, v))
                edge_set.add((v, u))
        edges = [[] for _ in range(n)]
        for (u, v) in edge_set:
            edges[u].append(v)
        balance = [0 for _ in range(n)]
        debt = rng.randint(1, n - 1)
        for _ in range(debt):
            balance[rng.randint(0, n - 1)] -= 1
        no_debt = [u for u in range(n) if balance[u] >= 0]
        for _ in range(debt + rng.randint(m, 2*m - n)):
            balance[rng.choice(no_debt)] += 1
        yield edges, balance


def recaman_generator(seed):
    for n in range(1, 1000001):
        yield n,


def is_caterpillar_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(5, 1, 1), 2000):
        edges = [[] for _ in range(n)]
        m = rng.randint(2, n - 2)
        for u in range(1, m):
            edges[u].append(u - 1)
            edges[u - 1].append(u)
        for u in range(m, n):
            if rng.randint(0, 99) < 80:
                v = rng.randint(0, m - 1)
            else:
                v = rng.randint(0, u - 1)
            edges[u].append(v)
            edges[v].append(u)
        perm = list(range(n))
        rng.shuffle(perm)
        inv = [0 for _ in range(n)]
        for (i, e) in enumerate(perm):
            inv[e] = i
        edges = [[perm[v] for v in edges[inv[u]]] for u in range(n)]
        while rng.randint(0, 99) < 20:
            if rng.randint(0, 99) < 80:
                u = rng.randint(0, n - 1)
                v = rng.randint(0, n - 1)
                if u != v and v not in edges[u]:
                    edges[u].append(v)
                    edges[v].append(u)
            else:
                u = rng.randint(0, n - 1)
                if len(edges[u]) > 0:
                    v = rng.choice(edges[u])
                    edges[u].remove(v)
                    edges[v].remove(u)
        for e in edges:
            e.sort()
        yield edges,


def sneaking_generator(seed):
    def choose():
        x = rng.randint(0, n - 1)
        y = rng.randint(0, n - 1)
        while (x, y) in knights:
            x = rng.randint(0, n - 1)
            y = rng.randint(0, n - 1)
        return (x, y)

    rng = Random(seed)
    for n in islice(pyramid(4, 6, 7), 100):
        knights = set()
        m = rng.randint(n // 2, n + 1)
        while len(knights) < m:
            x = rng.randint(0, n - 1)
            y = rng.randint(0, n - 1)
            knights.add((x, y))
        (gx, gy) = choose()
        while True:
            (kx, ky) = choose()
            is_ok = True
            for (xx, yy) in knights:
                for (dx, dy) in __knight_moves:
                    if (kx, ky) == (xx + dx, yy + dy):
                        is_ok = False
                        break
                if not is_ok:
                    break
            if is_ok:
                yield n, (kx, ky), (gx, gy), list(knights)
                break


def first_fit_bin_packing_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 1, 1), 3000):
        items = [rng.randint(1, 2*n) for _ in range(n)]
        m = max(items)
        capacity = rng.randint(m, 3 * m)
        yield items, capacity


def word_bin_packing_generator(seed):
    rng = Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [w.strip() for w in f if len(w) == 5]
    for n in islice(pyramid(3, 1, 1), 250):
        yield rng.sample(words, n),


def word_positions_generator(seed):
    yield 'Buffalo buffalo Buffalo buffalo buffalo buffalo Buffalo buffalo', 'buffalo'
    yield 'James while John had had had had had had had had had had had a better effect on the teacher', 'had'
    yield 'That that is is that that is not is not is that it it is', 'that'
    yield 'That that is is that that is not is not is that it it is', 'is'
    rng = Random(seed)
    words = [random_string(ups + lows, rng.randint(1, 10), rng) for _ in range(100)]
    for n, p in islice(zip(pyramid(2, 1, 1), cycle([20, 50, 80])), 2000):
        sentence = []
        for i in range(n):
            if i > 0 and rng.randint(0, 99) < p:
                sentence.append(rng.choice(sentence))
            else:
                sentence.append(rng.choice(words))
        yield " ".join(sentence), rng.choice(sentence)


def __graph_generator(rng):
    for n, w in zip(pyramid(5, 2, 1), cycle(range(3, 8))):
        edge_set = set()
        m = 2 * rng.randint(n, 2*n)
        while len(edge_set) < m:
            u = rng.randint(0, n - 1)
            s = rng.randint(1, w)
            s = s * rng.choice([-1, +1])
            v = (u + s) % n
            if u != v:
                edge_set.add((u, v))
                edge_set.add((v, u))
        edges = [[] for _ in range(n)]
        for (u, v) in edge_set:
            edges[u].append(v)
        yield edges,


def independent_dominating_set_generator(seed):
    yield from islice(__graph_generator(Random(seed)), 200)


def vertex_cover_generator(seed):
    yield from islice(__graph_generator(Random(seed)), 800)


def spiral_matrix_generator(seed):
    rng = Random(seed)
    # Try all positions of all spiral matrices up to size 5 systematically
    for n in range(1, 6):
        for row in range(n):
            for col in range(n):
                yield n, row, col
    # Rest with random fuzzing
    for n in range(6, 500):
        for _ in range(n//2):
            row = rng.randint(0, n - 1)
            col = rng.randint(0, n - 1)
            yield n, row, col


def unity_partition_generator(seed):
    for n in range(78, 200):
        yield n,


def jai_alai_generator(seed):
    rng = Random(seed)
    yield 2, 'WLWL'
    yield 2, 'LLLLLL'
    yield 4, 'WWWWWWWWW'
    for n, m, p in islice(zip(pyramid(3, 15, 20), pyramid(4, 2, 2), cycle([30, 40, 50])), 2000):
        results = [rng.choice('WL')]
        for _ in range(m):
            result = results[-1] if rng.randint(0, 99) < p else rng.choice('WL')
            results.append(result)
        yield n, "".join(results)


def __random_frac(rng, p):
    if rng.randint(0, 99) < p:
        den = rng.randint(2, 10)
        num = rng.randint(1, den)
        return F(num, den)
    else:
        den = rng.randint(10, 100)
        num = rng.randint(den // 2, den)
        return F(num, den)


def tic_tac_generator(seed):
    rng = Random(seed)
    for p in islice(cycle([10, 20, 30, 40]), 100):
        board = [['.', '.', '.'], ['.', '.', '.'], ['.', '.', '.']]
        probs = [[__random_frac(rng, p) for _ in range(3)] for _ in range(3)]
        for _ in range(rng.randint(6, 8)):
            row = rng.randint(0, 2)
            col = rng.randint(0, 2)
            mark = rng.choice("XO")
            board[row][col] = mark
        yield board[:], 'X', probs
        yield board[:], 'O', probs


def lowest_fraction_between_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 1, 1), 3000):
        a = rng.randint(1, 3*n)
        b = n
        if rng.randint(0, 99) < 50:
            c = rng.randint(1, n)
            d = rng.randint(n+1, n*n)
        else:
            c = rng.randint(a, a+2)
            d = rng.randint(b-1, b+1)
        first = F(a, b)
        second = first + F(c, d)
        first, second = min(first, second), max(first, second)
        yield first, second


def lamp_pairs_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 1, 1), 500):
        lamps = "".join([rng.choice("01") for _ in range(n)])
        if lamps.count('0') % 2 == 1:
            lamps += '0'
        yield lamps,


def count_friday_13s_generator(seed):
    rng = Random(seed)
    days_in_month = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

    def random_date(n):
        year = 2024 + rng.randint(-n, n)
        month = rng.randint(1, 12)
        is_leap_year = year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)
        if rng.randint(0, 99) < 20:
            day = rng.randint(12, 14)
        elif month == 2 and is_leap_year:
            day = rng.randint(1, 29)
        else:
            day = rng.randint(1, days_in_month[month])
        return date(year, month, day)

    for n in islice(pyramid(1, 2, 2), 3000):
        start = random_date(n)
        end = random_date(n)
        yield (start, end) if start <= end else (end, start)


def twos_and_threes_generator(seed):
    for n in islice(scale_random(seed, 2, 2), 600):
        yield n,


def infected_cells_generator(seed):
    yield [(0, 0), (1, 1), (1, 3), (3, 2)],
    rng = Random(seed)
    for n in islice(pyramid(2, 2, 2), 2000):
        infected = set()
        x = rng.randint(-n, n)
        y = rng.randint(-n, n)
        while len(infected) < n:
            infected.add((x, y))
            if rng.randint(0, 99) < 20:
                x = rng.randint(-n, n)
                y = rng.randint(-n, n)
            else:
                x += rng.choice([-2, -1, -1, 0, 1, 1, 2])
                y += rng.choice([-2, -1, -1, 0, 1, 1, 2])
        yield list(infected),


def knight_jam_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 5, 6), 100):
        knights = set()
        while len(knights) < n:
            x = rng.randint(0, 2 + n // 2)
            y = rng.randint(0, 2 + n // 2)
            knights.add((x, y))
        yield knights, rng.randint(0, 1)


def arithmetic_skip_generator(seed):
    rng = Random(seed)
    for n in range(6000):
        yield rng.choice([-n, n]),


def trip_flip_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(5, 5, 6), 1300):
        yield [rng.randint(0, 3) for _ in range(n)],


def square_lamps_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 2), 3000):
        flips = []
        for _ in range(rng.randint(n, 3*n)):
            i = rng.randint(1, n)
            sign = rng.choice([-1, 1])
            flips.append(i * sign)
        yield n, flips


def lychrel_generator(seed):
    for n, giveup in zip(range(100, 20000), pyramid(100, 5, 5)):
        yield n, giveup


def nfa_generator(seed):
    rng = Random(seed)

    def sample(n):
        if rng.randint(0, 99) < 20:
            return []
        else:
            return rng.sample(range(0, n), n - isqrt(isqrt(rng.randint(1, n*n*n*n))))

    for n, m in islice(zip(pyramid(2, 3, 4), pyramid(2, 5, 5)), 1000):
        alpha = lows[:m]
        rules = {(s, c): sample(n) for s in range(n) for c in alpha}
        text = random_string(alpha, rng.randint(n, 2 * n), rng)
        yield rules, text


def dfa_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(2, 3, 4), pyramid(2, 5, 5)), 1000):
        alpha = lows[:m]
        rules = {(s, c):rng.randint(0, n-1) for s in range(n) for c in alpha}
        text = random_string(alpha, rng.randint(n, 2*n), rng)
        yield rules, text


def repeating_decimal_generator(seed):
    for s in range(2, 500):
        for n in range(s//2 + 1, s):
            if gcd(s-n, n) == 1:
                yield s-n, n


def shapley_shubik_generator(seed):
    yield [1, 1, 1, 1, 1], 3
    yield [4, 1, 1, 1], 4
    yield [3, 1, 1, 1], 4
    rng = Random(seed)
    m = 5
    for n in islice(pyramid(3, 2, 2), 50):
        weight = sorted([rng.randint(1, m) for _ in range(n)], reverse = True)
        s = sum(weight) // 4
        quota = rng.randint(2*s+1, 3*s)
        yield weight, quota
        m += 1


def pair_swaps_generator(seed):
    for n in range(1, 7):
        for p in permutations(range(n)):
            yield list(p),
    rng = Random(seed)
    items = list(range(8))
    for n in islice(pyramid(8, 5, 5), 10000):
        if len(items) < n:
            items.append(n-1)
        rng.shuffle(items)
        yield items[:]


def pair_sums_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 3, 3), pyramid(4, 2, 1)), 150):
        nums = [rng.randint(1, 3)]
        for _ in range(n-1):
            nums.append(nums[-1] + rng.randint(1, m))
        sums = sorted(x+y for (x, y) in combinations(nums, 2))
        yield n, sums


def count_triangles_generator(seed):
    rng = Random(seed)
    yield [42],
    yield [1, 2],
    yield [1, 2, 3],
    for n, d in islice(zip(pyramid(4, 1, 1), cycle([1, 2, 3, 2, 1])), 1000):
        sides = [rng.randint(1, n)]
        sides.append(sides[0] + rng.randint(1, n))
        for _ in range(n-2):
            sides.append(sides[-1] + d * rng.randint(1, sides[-1] - sides[-2]))
        yield sides,


def place_disks_generator(seed):
    rng = Random(seed)
    for (n, r) in islice(zip(pyramid(3, 2, 2), pyramid(2, 3, 4)), 300):
        points, rr = set(), 3*r
        x = rng.randint(-rr, rr)
        y = rng.randint(-rr, rr)
        while len(points) < n:
            points.add((x, y))
            x = abs(x + rng.randint(-rr, rr))
            y = abs(y + rng.randint(-rr, rr))
        yield list(points), r


def longest_zigzag_generator(seed):
    rng = Random(seed)
    for n, r in islice(zip(pyramid(2, 2, 2), pyramid(4, 4, 4)), 2000):
        items = [rng.randint(1, 2*r)]
        for _ in range(n-1):
            items.append(abs(items[-1] + rng.randint(-r, r)))
        yield items,


def median_filter_generator(seed):
    yield [42], 7
    yield [17, 19], 3
    rng = Random(seed)
    for (n, r, p) in islice(zip(pyramid(3, 2, 2), pyramid(4, 4, 5), cycle([10, 20, 30])), 3000):
        m = rng.randint(-2*r, 2*r)
        items = []
        for _ in range(n):
            d = rng.randint(-r, r)
            items.append(m + (10 * d if rng.randint(0, 99) else d))
            m += d
        k = 3
        while rng.randint(0, 99) < 30:
            k += 2
        yield items, k


def domino_pop_generator(seed):
    rng = Random(seed)
    yield [(1, 2)],
    yield [(2, 5), (5, 1)],
    yield [(2, 4), (2, 4)],
    for (n, p) in islice(zip(pyramid(3, 4, 4), cycle([25, 60, 75])), 800):
        dominos = []
        for _ in range(n):
            if len(dominos) > 0 and rng.randint(0, 99) < p:
                s1 = dominos[-1][1]
            else:
                s1 = rng.randint(0, 6)
            s2 = rng.randint(0, 6)
            dominos.append((s1, s2))
        yield dominos,


def self_describe_generator(seed):
    yield [1],
    yield [1, 2],
    yield [1, 2, 3],
    yield [2, 2, 5, 5, 5, 5],
    yield [1, 4, 4, 4],
    rng = Random(seed)
    for (n, p) in islice(zip(pyramid(3, 4, 5), cycle([10, 40, 80])), 2000):
        m = rng.randint(3, n)
        items = []
        for _ in range(n):
            if len(items) > 1 and rng.randint(0, 99) < p:
                x = rng.choice(items)
            else:
                x = rng.randint(1, m)
            items.append(x)
        yield items,


def arrow_walk_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 2), 5000):
        board = [rng.choice("<>") for _ in range(n)]
        yield "".join(board), rng.choice(range(n))


def itky_leda_generator(seed):
    yield [[1, 0], [0, 1]],
    yield [[1, 2, 4, 3], [3, 4, 1, 2], [3, 1, 2, 3], [2, 3, 1, 2]],
    rng = Random(seed)
    for n in islice(pyramid(3, 6, 7), 300):
        yield [[n - 1 - isqrt(rng.randint(0, n*n-1)) for _ in range(n)] for _ in range(n)],
        yield [[isqrt(rng.randint(0, n*n-1)) for _ in range(n)] for _ in range(n)],


def lowest_common_dominator_generator(seed):
    rng = Random(seed)
    m = 2
    for n in islice(pyramid(2, 2, 2), 3000):
        beta = [rng.randint(-m, m) for _ in range(n)]
        gamma = [rng.randint(-m, m) for _ in range(n)]
        yield beta, gamma
        m += 1


def str_rts_generator(seed):
    for text in ["", "x", "abcd", "bb", "aaa", "hahahexoxehah", "abcdefgfoooof", "bxuzazuxbzuzax"]:
        yield text,
    rng = Random(seed)
    for n in islice(pyramid(10, 2, 2), 7500):
        text = ""
        while len(text) < n:
            if len(text) < 3 or rng.randint(0, 100) < 50:
                text += rng.choice(lows)
            else:
                i = rng.randint(0, len(text))
                j = rng.randint(0, len(text))
                i, j = min(i, j), max(i, j)
                text += text[j:i-1:-1] if rng.randint(0, 100) < 70 else text[i:j+1]
        yield text,


def is_string_shuffle_generator(seed):
    rng = Random(seed)
    for _ in range(1000):
        names = rng.sample(__names, 2)
        name1, name2 = names[0], names[1]
        n1, n2 = len(name1), len(name2)
        result, i, j = "", 0, 0
        while len(result) < n1 + n2:
            if j < n2 and (i == n1 or rng.randint(0, 99) < 50):
                result += name2[j]
                j += 1
            else:
                result += name1[i]
                i += 1
        while rng.randint(0, 100) < 50:
            i = rng.randint(0, n1 + n2 - 1)
            j = rng.randint(0, n1 + n2 - 1)
            if i < j:
                result = result[:i] + result[j] + result[i + 1:j] + result[i] + result[j + 1:]
            elif j < i:
                result = result[:j] + result[i] + result[j + 1:i] + result[j] + result[i + 1:]
        yield name1, name2, result


def count_cigarettes_generator(seed):
    yield 25, 5
    rng = Random(seed)
    for n in range(5, 1000):
        for k in rng.sample(range(2, n + 1), min(10, n - 1)):
            yield n, k
    for n in islice(scale_random(seed, 2, 5), 1000):
        n += 2000
        k = rng.randint(2, 100)
        yield n, k


def van_der_corput_generator(seed):
    rng = Random(seed)
    for base, n in islice(zip(pyramid(2, 3, 3), count(1)), 1000):
        yield base, rng.randint(1, n)


def super_tiny_rng_generator(seed):
    rng = Random(seed)
    for n, bits in islice(zip(pyramid(3, 10, 2), cycle(range(8, 65))), 1000):
        yield rng.randint(0, 2 ** 32 - 1), n, bits


def minimal_egyptian_generator(seed):
    for ft, k in islice(zip(greedy_egyptian_generator(seed), cycle([2, 3, 4])), 2500):
        f = ft[0]
        if f.denominator > 50:
            yield f, k


def greedy_egyptian_generator(seed):
    rng = Random(seed)
    b = 5
    for n in islice(pyramid(3, 5, 6), 1000):
        for _ in range(n):
            a = rng.randint(2, b - 1)
            yield F(a, b),
        b += 1


def kayles_generator(seed):
    rng = Random(seed)
    for n in range(1, 10):
        yield [n],
    for n in range(2, 12):
        for p in range(n):
            yield [n, p],
    for n in range(3, 12):
        for m in range(n, 4 * n):
            piles = [0 for _ in range(n)]
            for _ in range(m):
                piles[rng.randint(0, n - 1)] += 1
            piles = [p for p in piles if p > 0]
            yield piles,


def reversenacci_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 5, 6), 250):
        a = rng.randint(1, n)
        b = rng.randint(a, a + n + 1)
        i = 1
        for _ in range(rng.randint(1, 2 * n)):
            a, b = b, a + b
            i += 1
        yield i, b
        yield i, b + 1
        yield i, b - 1


def carryless_multiplication_generator(seed):
    yield 0, 10
    yield 12, 0
    rng = Random(seed)
    for n, p in islice(zip(pyramid(2, 1, 1), cycle([20, 40, 60, 80])), 1000):
        m = rng.randint(1, n)
        a = random_int(rng, n, p)
        b = random_int(rng, m, p)
        yield a, b


def game_with_multiset_generator(seed):
    yield [('A', 0), ('A', 0), ('A', 2), ('G', 6)]
    powers = [2 ** i for i in range(100)]
    rng = Random(seed)
    for n, m in islice(zip(pyramid(10, 3, 3), pyramid(3, 2, 3)), 300):
        queries, total, used = [], 0, []
        for i in range(n):
            if i < n - 1 and (i < 3 or rng.randint(0, 99) < 50):
                val = rng.randint(0, m)
                queries.append(('A', val))
                used.append(val)
                total += powers[val]
            else:
                if rng.randint(0, 99) < 50:
                    queries.append(('G', rng.randint(0, total)))
                else:
                    val = 0
                    for x in rng.sample(used, rng.randint(2, len(used))):
                        val += powers[x]
                    queries.append(('G', val))
        yield queries,


def nice_sequence_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(6, 3, 3), 200):
        items = rng.sample(range(2, 20 * n), 4)
        while len(items) < n:
            c = rng.choice(items)
            if rng.randint(0, 99) < 50:
                c *= rng.choice(range(2, 7))
            else:
                c = c // rng.choice(range(2, 7))
            if c > 1 and c not in items:
                items.append(c)
        yield sorted(items), rng.choice(items)


def prize_strings_generator(seed):
    rng = Random(seed)
    for n in range(4, 60):
        for _ in range(3):
            late_limit = rng.randint(1, 4)
            absent_limit = rng.randint(2, 6)
            yield n, late_limit, absent_limit


def goodstein_generator(seed):
    rng = Random(seed)
    for n in range(1, 200):
        yield n, rng.randint(1, n)
        yield n, rng.randint(2 * n, 3 * n)
        yield n, rng.randint(10 * n, 20 * n)


def max_product_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(4, 2, 2), 400):
        digits = [str(rng.randint(0, 9)) for _ in range(n)]
        digits.sort(reverse=True)
        m = rng.randint(1, n - 1)
        yield "".join(digits), max(n - m, m), min(n - m, m)


def count_unicolour_rectangles_generator(seed):
    yield ["c"],
    yield ["aa", "aa"],
    yield ["aba", "ccc", "ada"],
    yield ["ddd", "ddd", "ddd"],
    yield ["aba", "bab", "aba"],
    yield ["ccc", "ccc", "ccc", "ccc"],
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 2), 400):
        m = rng.randint(1, 2 * n)
        grid = ["".join(rng.choice("abcd") for _ in range(m)) for _ in range(n)]
        yield grid,


def markov_distance_generator(seed):
    rng = Random(seed)
    triples_list = [(1, 2, 5), (13, 34, 1325), (2, 29, 169)]
    triples_set = set(triples_list)
    while len(triples_list) < 400:
        triple = list(rng.choice(triples_list))
        rng.shuffle(triple)
        (x, y, z) = triple
        succ = tuple(sorted([x, y, 3 * x * y - z]))
        if succ not in triples_set:
            triples_set.add(succ)
            triples_list.append(succ)
    for n in range(400):
        i1 = rng.randint(0, n)
        i2 = rng.randint(0, n)
        yield triples_list[i1], triples_list[i2]


def gijswijt_generator(seed):
    rng = Random(seed)
    n = 0
    for m in islice(pyramid(3, 1, 1), 300):
        yield n,
        nn = n + rng.randint(1, m)
        if n < 219 < nn:
            yield 219,
        n = nn


def parking_lot_permutation_generator(seed):
    rng = Random(seed)
    yield [0],
    yield [1, 0],
    yield [1, 1],
    yield [0, 0]
    for n, p in islice(zip(pyramid(3, 1, 1), cycle([20, 50, 70])), 1000):
        preferred_spot = list(range(n))
        rng.shuffle(preferred_spot)
        for i in range(n):
            if rng.randint(0, 99) < p:
                preferred_spot[i] = rng.choice(preferred_spot)
        yield preferred_spot,


def tower_of_babel_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(2, 2, 2), pyramid(7, 1, 1)), 100):
        blocks = []
        for _ in range(n):
            x = rng.randint(1, m)
            y = rng.randint(1, m)
            z = rng.randint(1, m)
            blocks.append((x, y, z))
        yield blocks,


def vector_add_reach_generator(seed):
    rng = Random(seed)
    for n, d in islice(zip(pyramid(2, 8, 10), cycle(range(2, 11))), 250):
        m, vectors = rng.randint(max(2, n - 2), n), set()
        while len(vectors) < m:
            v = tuple(rng.randint(-m, m) for _ in range(d))
            if any(c != 0 for c in v):
                vectors.add(v)
        vectors = list(vectors)
        start = goal = 0
        while start == goal:
            if rng.randint(0, 99) < 20:
                coords = [rng.randint(0, 2 * n) for _ in range(2 * d)]
                start = tuple(coords[:d])
                goal = tuple(coords[d:])
            else:
                goal = start = tuple(rng.randint(n, 3 * n) for _ in range(d))
                for _ in range(rng.randint(2 * n, 3 * n)):
                    step = tuple(x + y for (x, y) in zip(goal, rng.choice(vectors)))
                    if all(c >= 0 for c in step):
                        goal = step
        yield start, goal, vectors, 3 * n


def mmu_generator(seed):
    rng = Random(seed)
    for n, m, p in chain(
            islice(zip(pyramid(2, 8, 10), pyramid(5, 3, 4), cycle([20, 35, 60])), 2000),
            islice(zip(pyramid(20, 2, 2), range(100, 600), cycle([10, 20, 30])), 500)
    ):
        pages = []
        while len(pages) < m:
            if len(pages) < 3 or rng.randint(0, 99) < p:
                p = rng.randint(0, 2 * n)
            else:
                p = rng.choice(pages)
            pages.append(p)
        yield rng.randint(1, n + 1), pages


def count_distinct_substrings_generator(seed):
    rng = Random(seed)
    yield "",
    yield "a",
    yield "ab",
    yield "bb",
    for n, p in islice(zip(pyramid(3, 2, 2), cycle([10, 50, 90])), 2000):
        text = [rng.choice(lows) for _ in range(3)]
        i = rng.randint(0, 2)
        while len(text) < n:
            if i == len(text) or rng.randint(0, 99) < p:
                text.append(rng.choice(lows))
                i = rng.randint(0, len(text) - 1)
            else:
                text.append(text[i])
                if rng.randint(0, 99) < 30:
                    i += 1
        yield "".join(text),
    # Don't be a Shlemiel.
    yield "abc" * 500,
    yield "xyx" * 501
    yield "brrr" * 400


def measure_balsam_generator(seed):
    rng = Random(seed)
    for n, m in islice(zip(pyramid(3, 50, 10), pyramid(8, 2, 2)), 400):
        flasks = sorted([rng.randint(1, m) for _ in range(n)], reverse=True)
        flasks[0] += 1
        goal = rng.randint(1, flasks[0] - 1)
        while goal in flasks:
            goal = rng.randint(1, flasks[0] - 1)
        yield tuple(flasks), goal


def digit_partition_generator(seed):
    # Some systematic test cases to reveal most bugs
    yield from [("1", 1), ("12", 3), ("12", 12), ("123", 6), ("123", 24), ("1234", 10), ("1234", 28),
                ("1234", 127), ("1234", 235), ("1234", 1234), ("1234", 19), ("1234", 37), ("1234", 1234)]
    # The rest with fuzzing
    rng = Random(seed)
    for (n, d) in islice(zip(pyramid(5, 6, 6), pyramid(4, 5, 6)), 300):
        digits, goal = "", 0
        while len(digits) < n:
            m = random_string("0123456789", rng.randint(1, d), rng)
            goal += int(m)
            digits += m
        if rng.randint(0, 99) < 50:
            off = goal // 10
            goal = rng.randint(goal - off, goal + off)
        yield digits, goal


def tr_generator(seed):
    alphabet = string.ascii_letters + string.digits
    rng = Random(seed)
    yield "abc", "", ""
    yield "", "X", "Y"
    yield "X", "Z", "Y"
    yield "ab", "ab", "ba"
    for n in islice(pyramid(2, 2, 2), 2000):
        k = rng.randint(1, n + 5)
        text = "".join([rng.choice(alphabet[:n + 2]) for _ in range(n)])
        ch_from = "".join(rng.sample(alphabet[:n + 5], k))
        ch_to = "".join(rng.choices(alphabet[:n + 10], k=k))
        yield text, ch_from, ch_to


def cube_tower_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 1), 400):
        cubes, m = [], rng.randint(n + 1, n + 6)
        for _ in range(n):
            cubes.append([rng.randint(0, m - 1) for _ in range(6)])
        yield cubes,


def des_chiffres_generator(seed):
    rng = Random(seed)
    for n, s in islice(zip(pyramid(3, 5, 5), pyramid(10, 2, 1)), 100):
        board = sorted([rng.randint(1, s) for _ in range(n)])
        goal = board[-1]
        while goal in board:
            goal = rng.randint(1, n * s * 4)
        yield board, goal


def fewest_boxes_generator(seed):
    rng = Random(seed)
    yield [], 42
    yield [41], 42
    s = 5
    for n in islice(pyramid(2, 1, 1), 4000):
        items = [rng.randint(1, s)]
        for _ in range(n):
            items.append(items[-1] + rng.randint(1, s))
        yield items, items[-1] + rng.randint(1, s)
        s += 1


def squares_total_area_generator(seed):
    rng = Random(seed)
    yield [(3, 4)],
    yield [(2, 2), (3, 3), (4, 4), (3, 3), (2, 2)],
    yield [(6, 2), (5, 3), (9, 4)],
    yield [(9, 4), (6, 2), (5, 3)],
    yield [(5, 7), (8, 5)],
    yield [(3, 3), (5, 5), (7, 3)],
    yield [(6, 4), (3, 7)],
    yield [(3, 2), (3, 1)],
    yield [(2, 2), (5, 5), (6, 2)],
    s = 5
    for n in islice(pyramid(2, 1, 1), 2000):
        points = []
        for m in range(n):
            if m < 3 or rng.randint(0, 99) < 70:
                x = rng.randint(0, s)
                y = rng.randint(0, s)
            else:
                x = points[rng.randint(0, m - 1)][0]
                y = points[rng.randint(0, m - 1)][1]
            points.append((x, y))
            s += 1
        yield points,


def bridge_score_generator(seed):
    rng = Random(seed)
    for level in range(1, 8):
        for vul in [True, False]:
            for doubled in ['-', 'X', 'XX']:
                for strain in ['diamonds', 'clubs', 'hearts', 'spades', 'notrump']:
                    made = rng.randint(level, min(level + 3, 7))
                    yield strain, level, vul, doubled, made


def trip_plan_generator(seed):
    rng = Random(seed)
    step = 20
    for n in islice(pyramid(1, 1, 1), 2000):
        motels = [rng.randint(1, step // 2)]
        while len(motels) < n:
            motels.append(motels[-1] + rng.randint(5, step // 2))
        yield motels, rng.randint(motels[-1] // 20 + 2, motels[-1] // 2 + 2)
        step += 2


def tog_comparison_generator(seed):
    alpha = ups + lows + "0123456789.!@#$%^&*()[]{}"
    rng = Random(seed)
    for n, p in islice(zip(pyramid(5, 2, 2), cycle([40, 70, 90])), 2000):
        first, second = "", ""
        while len(first) < n:
            if rng.randint(0, 99) < 50:
                ch1 = rng.choice(alpha)
                ch2 = ch1 if rng.randint(0, 99) < p else rng.choice(alpha)
            else:
                ch1 = rng.randint(0, 10 ** (n - 2))
                ch2 = rng.randint(0, 10 ** (n - 3)) if rng.randint(0, 99) < p else ch1
            first, second = first + str(ch1), second + str(ch2)
        suffix = rng.choice([".txt", ".doc", ".dat", ".xls", ".jpg"])
        first += suffix
        second += suffix
        if first != second:
            yield first, second
            yield second, first
        yield first, first


def repetition_resistant_generator(seed):
    yield from range(10000)


def kimberling_expulsion_generator(seed):
    rng = Random(seed)
    start = 0
    for n in range(100):
        end = start + rng.randint(1, n + 2)
        yield start, end
        start = end


def hofstadter_figure_figure_generator(seed):
    for n in range(0, 100001):
        yield n,


def langford_violations_generator(seed):
    # Some known Langford sequences
    yield [3, 1, 2, 1, 3, 2],
    yield [4, 1, 3, 1, 2, 4, 3, 2],
    yield [2, 3, 4, 2, 1, 3, 1, 4],
    yield [5, 2, 8, 6, 2, 3, 5, 7, 4, 3, 6, 8, 1, 4, 1, 7],
    yield [5, 8, 4, 1, 7, 1, 5, 4, 6, 3, 8, 2, 7, 3, 2, 6],
    rng = Random(seed)
    flip = True
    for k in islice(pyramid(3, 2, 4), 2000):
        n = 4 * k - (1 if flip else 0)
        flip = not flip
        items = [None for _ in range(2 * n)]
        indices = list(range(1, n + 1))
        rng.shuffle(indices)
        unpaired = []
        for e in indices:
            i = rng.randint(e + 1, 2 * n - 1)
            if items[i] is None and items[i - (e + 1)] is None:
                items[i] = items[i - (e + 1)] = e
            else:
                unpaired.append(e)
        unfilled = [i for i in range(2 * n) if items[i] is None]
        rng.shuffle(unfilled)
        i = 0
        for e in unpaired:
            items[unfilled[i]] = items[unfilled[i + 1]] = e
            i += 2
        yield items


def shotgun_generator(seed):
    for n in islice(scale_random(seed, 2, 5), 100):
        yield n,


def count_palindromes_generator(seed):
    yield 'a',
    yield 'aa',
    yield 'ab',
    rng = Random(seed)
    for n, p in islice(zip(pyramid(1, 1, 1), cycle([30, 50, 80])), 3000):
        text = ""
        while len(text) < n:
            if len(text) > 4 and rng.randint(0, 99) < p:
                i = rng.randint(-1, len(text) - 1)
                text += text[-1:i:-1]
            else:
                text += rng.choice(('a', 'b', 'ab', 'ba', 'aa', 'bb'))
        yield text,


def mu_torere_moves_generator(seed):
    board = 'BW-'
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 2), 1000):
        yield board, 'W'
        yield board, 'B'
        if n > len(board):
            board += 'BW'
        board_l = [p for p in board]
        rng.shuffle(board_l)
        board = "".join(board_l)


def discrete_rounding_generator(seed):
    for n in range(1, 4000):
        yield n,


def stern_brocot_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 2), 10000):
        den = rng.randint(n, 2 * n)
        num = rng.randint(1, 2 * den)
        yield F(num, den),


def abacaba_generator(seed):
    rng = Random(seed)
    for n in range(2 ** 5 - 1):
        yield n,
    for m, p in zip(islice(pyramid(5, 1, 1), 10000), cycle([30, 60, 95])):
        n = 2 ** m - 1
        while m > 0 and rng.randint(0, 99) < p:
            m = m - 1
            n = n + (1 if rng.randint(0, 1) else -1) * 2 ** m
        yield n,
        yield n + rng.randint(1, n // 3)


__keys = {'a': 2, 'b': 2, 'c': 2, 'd': 3, 'e': 3, 'f': 3, 'g': 4, 'h': 4, 'i': 4,
          'j': 5, 'k': 5, 'l': 5, 'm': 6, 'n': 6, 'o': 6, 'p': 7, 'q': 7, 'r': 7,
          's': 7, 't': 8, 'u': 8, 'v': 8, 'w': 9, 'x': 9, 'y': 9, 'z': 9}


def keypad_words_generator(seed):
    rng = Random(seed)
    digits = [2, 2, 3, 3, 3, 4, 5, 5, 6, 6, 7, 7, 8, 8, 8, 9]
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [w.strip() for w in f if 3 < len(w) < 9]
    yield '3287448', words
    yield '4444444', words
    for _ in range(500):
        number = "".join(str(rng.choice(digits)) for _ in range(7))
        yield number, words
        while True:
            word = rng.choice(words)
            if len(word) == 7:
                yield "".join(str(__keys[c]) for c in word), words
                break


def break_bad_generator(seed):
    rng = Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [w.strip() for w in f if len(w) > 2]
    elements = ['H', 'He', 'Li', 'Be', 'B', 'C', 'N', 'O', 'F', 'Ne', 'Na', 'Mg', 'Al', 'Si', 'P', 'S', 'Cl', 'Ar',
                'K', 'Ca', 'Sc', 'Ti', 'V', 'Cr', 'Mn', 'Fe', 'Co', 'Ni', 'Cu', 'Zn', 'Ga', 'Ge', 'As', 'Se', 'Br',
                'Kr', 'Rb', 'Sr', 'Y', 'Zr', 'Nb', 'Mo', 'Tc', 'Ru', 'Rh', 'Pd', 'Ag', 'Cd', 'In', 'Sn', 'Sb', 'Te',
                'I', 'Xe', 'Cs', 'Ba', 'La', 'Ce', 'Pr', 'Nd', 'Pm', 'Sm', 'Eu', 'Gd', 'Tb', 'Dy', 'Ho', 'Er', 'Tm',
                'Yb', 'Lu', 'Hf', 'Ta', 'W', 'Re', 'Os', 'Ir', 'Pt', 'Au', 'Hg', 'Tl', 'Pb', 'Bi', 'Po', 'At', 'Rn',
                'Fr', 'Ra', 'Ac', 'Th', 'Pa', 'U', 'Np', 'Pu', 'Am', 'Cm', 'Bk', 'Cf', 'Es', 'Fm', 'Md', 'No', 'Lr',
                'Rf', 'Db', 'Sg', 'Bh', 'Hs', 'Mt', 'Ds', 'Rg', 'Cn', 'Nh', 'Fl', 'Mc', 'Lv', 'Ts', 'Og']
    yield 'i', elements
    yield 'no', elements
    yield 'qx', elements
    yield 'felina', elements
    for word in rng.sample(words, 2000):
        yield word, elements


def forbidden_digit_generator(seed):
    yield 0, 7
    yield 1, 4
    yield 2, 9
    yield 3, 3
    for n, d in islice(zip(scale_random(seed, 5, 3), cycle(range(10))), 1000):
        yield n, d


def blocking_pawns_generator(seed):
    rng = Random(seed)
    dirs = [(0, 0), (0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1)]
    for n in islice(pyramid(8, 3, 3), 50):
        taken, queens = set(), []
        for _ in range(10):
            x = rng.randint(1, n - 2)
            y = rng.randint(1, n - 2)
            for (dx, dy) in rng.sample(dirs, rng.randint(2, 5)):
                d = rng.randint(2, 4)
                nx, ny = (x + d * dx) % n, (y + d * dy) % n
                for (ddx, ddy) in dirs:
                    if (nx + ddx, ny + ddy) in taken:
                        break
                else:
                    queens.append((nx, ny))
                    for (ddx, ddy) in dirs:
                        taken.add((nx + ddx, ny + ddy))
        yield n, queens


def optimal_blackjack_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(20, 2, 1), 2500):
        yield [rng.choice([2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 10, 10, 11]) for _ in range(n)],


def stalin_sort_generator(seed):
    yield [],
    yield [42],
    yield [1, 2],
    yield [2, 1],
    yield [42, 42],
    rng = Random(seed)
    m = 5
    for n in islice(pyramid(3, 1, 1), 1000):
        yield [rng.randint(-(m * m), (m * m)) for _ in range(n)],
        items = list(range(n, -n, -1))
        for _ in range(rng.randint(0, n // 2)):
            i = rng.randint(0, len(items) - 1)
            j = rng.randint(0, len(items) - 1)
            items[i], items[j] = items[j], items[j]
        yield items,


def smetana_interpreter_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 2), 4000):
        program = []
        for _ in range(n):
            if rng.randint(0, 99) < 50:
                s1 = rng.randint(0, n - 1)
                s2 = rng.randint(0, n - 1)
                while s1 == s2:
                    s2 = rng.randint(0, n - 1)
                program.append(f"SWAP {s1} {s2}")
            else:
                s = rng.randint(0, n - 1)
                program.append(f"GOTO {s}")
        yield program,


def card_row_game_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 2, 2), 1000):
        yield [rng.randint(1, n * n) for _ in range(n)],


def has_majority_generator(seed):
    yield [],
    yield [42],
    yield [1, 2, 1, 2],
    yield [49, 99],
    yield [17, 17, 99],
    yield [99, 42, 17],
    rng = Random(seed)
    for n, take, look in zip(islice(pyramid(3, 2, 1), 1000), cycle([30, 50, 90]), cycle([3, 4, 5, 6])):
        m = n * n
        items = [rng.randint(1, m) for _ in range(look)]
        for _ in range(m - look):
            items.append(rng.randint(1, n) if rng.randint(0, 99) < take else items[-rng.randint(1, look)])
        item = rng.choice(items)
        for _ in range(rng.randint(m // 4, m)):
            items[rng.randint(0, m - 1)] = item
        yield items


def bus_travel_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(4, 2, 1), 1000):
        schedule = {i: [] for i in range(n)}
        goal = rng.randint(1, n - 1)
        while len(schedule[0]) < 3:
            hour = rng.randint(1, 20)
            minute = rng.randint(0, 59)
            city = rng.randint(0, n - 1)
            legs = 0
            while legs < n:
                duration = rng.randint(10, 100)
                destination = rng.randint(0, n - 1)
                while city == destination:
                    destination = rng.randint(0, n - 1)
                arrive_m = minute + duration
                arrive_h, arrive_m = hour + arrive_m // 60, arrive_m % 60
                schedule[city].append((destination, (hour, minute), (arrive_h, arrive_m)))
                city, hour, minute = destination, arrive_h, arrive_m
                legs += 1
        for city in schedule:
            schedule[city].sort()
        yield schedule, goal


def multiplicative_persistence_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(5, 5, 5), 2000):
        m = rng.randint(1, 9)
        for _ in range(n):
            m = 10 * m + rng.choice([1, 2, 3, 4, 5, 6, 6, 7, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9])
        yield m, True
        yield m, False


def count_odd_sum_sublists_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 2, 2), 10000):
        yield [rng.randint(0, n) for _ in range(n)],


def largest_ones_square_generator(seed):
    rng = Random(seed)
    yield ['0'],
    yield ['1'],
    yield ['01', '10'],
    yield ['11', '11'],
    yield ['10', '11']
    for p, n in zip(cycle([30, 60, 80, 90]), islice(pyramid(3, 3, 3), 2000)):
        nn = n * n
        board = [['0' for _ in range(n)] for _ in range(n)]
        fill = rng.randint(nn // 4, (7 * nn) // 8)
        while fill > 0:
            x = rng.randint(0, n - 1)
            y = rng.randint(0, n - 1)
            w = 1
            while w < n - x and w < n - y and rng.randint(0, 99) < p:
                w += 1
            for xx in range(x, x + w):
                for yy in range(y, y + w):
                    if board[xx][yy] == '0':
                        fill -= 1
                        board[xx][yy] = '1'
        yield ["".join(row) for row in board],


def accumulate_dice_generator(seed):
    rng = Random(seed)
    for n in range(4, 20):
        d = 2
        while d < 2 * n:
            yield d, n
            d += rng.randint(1, 3)


def knight_survival_generator(seed):
    rng = Random(seed)
    for n in range(4, 20):
        for _ in range(n // 4 + 3):
            x = rng.randint(0, n - 1)
            y = rng.randint(0, n - 1)
            k = rng.randint(1, n)
            yield n, x, y, k


def bowling_score_generator(seed):
    rng = Random(seed)
    for (_, p) in zip(range(10000), cycle([10, 12, 16, 20])):
        rolls = []
        for pos in range(12):
            first = min(rng.randint(0, p), 10)
            if first == 10:
                rolls.append('X')
            else:
                remain = 10 - first
                second = min(rng.randint(0, remain + 3), remain)
                rolls.append(f"{first}/" if first + second == 10 else f"{first}{second}")
        # Last roll handled special
        if rolls[9] == 'X':
            rolls[9] = f"XX{rolls[11][0]}" if rolls[10] == 'X' else f"X{rolls[10]}"
        elif rolls[9][1] == '/':
            rolls[9] = rolls[9] + rolls[10][0]
        # Replace zeros with minus signs
        rolls = [frame.replace('0', '-') for frame in rolls]
        yield rolls[:10],


def word_board_generator(seed):
    rng = Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [w.strip() for w in f if len(w) > 5]
    long_words = [w for w in words if len(w) > 12]
    for n in islice(pyramid(3, 3, 4), 200):
        board = [[None for _ in range(n)] for _ in range(n)]
        unfilled = set((x, y) for x in range(n) for y in range(n))
        while len(unfilled) > 0:
            x = rng.randint(0, n - 1)
            y = rng.randint(0, n - 1)
            while (x, y) not in unfilled:
                x = rng.randint(0, n - 1)
                y = rng.randint(0, n - 1)
            for c in rng.choice(long_words):
                board[x][y] = c
                unfilled.remove((x, y))
                neighbours = []
                for dx, dy in [(0, 1), (1, 0), (0, -1), (-1, 0)]:
                    nx, ny = x + dx, y + dy
                    if 0 <= nx < n and 0 <= ny < n and (nx, ny) in unfilled:
                        neighbours.append((nx, ny))
                if len(neighbours) > 0:
                    x, y = rng.choice(neighbours)
                else:
                    break
        yield board, words


def lindenmayer_generator(seed):
    non_terminals = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
    rng = Random(seed)
    for r, steps in zip(islice(pyramid(3, 2, 1), 80), count(3)):
        rules = dict()
        alphabet = non_terminals[:r]
        for symbol in alphabet:
            m = rng.randint(2, r)
            rules[symbol] = random_string(alphabet, m, rng)
        seed += 1
        for n in islice(scale_random(seed, 10, 1), steps):
            yield rules, n, rng.choice(alphabet)


def mian_chowla_generator(seed):
    yield from range(200)


__primitive_roots = {
    5: [2, 3], 7: [3, 5], 11: [2, 6, 7, 8], 13: [2, 6, 7, 11], 17: [3, 5, 6, 7, 10, 11, 12, 14]
}


def __welch_costas():
    while True:
        for p in __primitive_roots:
            for g in __primitive_roots[p]:
                rows = []
                for i in range(1, p):
                    for j in range(1, p + 1):
                        if j == g ** i % p:
                            rows.append(j - 1)
                            break
                yield rows
                yield [p - 2 - col for col in rows]
                yield rows[::-1]
                yield [p - 2 - col for col in rows[::-1]]


def costas_array_generator(seed):
    rng = Random(seed)
    welch_generator = __welch_costas()
    for n in islice(pyramid(4, 4, 6), 400):
        if rng.randint(0, 99) < 50:
            rows = list(range(n))
            rng.shuffle(rows)
        else:
            rows = next(welch_generator)[:]
        m = len(rows)
        k = rng.randint(2, max(m // 2, m - 5))
        for row in rng.sample(range(m), k):
            rows[row] = None
        yield rows[:],


def topswops_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 3, 3), 5000):
        perm = list(range(1, n + 1))
        rng.shuffle(perm)
        yield tuple(perm),


def sum_of_consecutive_squares_generator(seed):
    def sum_of_sq(n_):  # Formula from Wolfram Mathematica
        return (n_ * (1 + n_) * (1 + 2 * n_)) // 6

    rng = Random(seed)
    d = 5
    for _ in range(400):
        hi = rng.randint(1, d)
        lo = rng.randint(1, d)
        hi, lo = max(hi, lo), min(hi, lo)
        n = sum_of_sq(hi) - sum_of_sq(lo - 1)
        for _ in range(rng.choice([0, 0, 0, 0, 0, 1, 1, 2, 3, 4])):
            m = rng.randint(1, hi)
            n += m * m * (1 if rng.randint(0, 1) else -1)
        yield max(n, 1)
        d += 4


def is_chess_960_generator(seed):
    rng = Random(seed)
    rows = ["".join(perm) for perm in permutations("KQrrkkbb")]
    rng.shuffle(rows)
    yield from [(row,) for row in rows]


__queen_dirs = [(0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1)]


def queen_captures_all_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(4, 4, 2), 350):
        m = n + rng.randint(0, 2)
        pieces = set()
        px = rng.randint(0, m - 1)
        py = rng.randint(0, m - 1)
        while len(pieces) < n:
            pieces.add((px, py))
            dx, dy = rng.choice(__queen_dirs)
            d = rng.randint(1, m // 2)
            px = (px + d * dx) % m
            py = (py + d * dy) % m
        pieces = list(pieces)
        yield pieces[0], pieces[1:]


def addition_chain_generator(seed):
    for n in range(1, 500):
        yield n, False
        yield n, True


__suits = ['clubs', 'diamonds', 'hearts', 'spades']

__bridge_ranks = {
    'two': 2, 'three': 3, 'four': 4, 'five': 5, 'six': 6, 'seven': 7, 'eight': 8, 'nine': 9,
    'ten': 10, 'jack': 11, 'queen': 12, 'king': 13, 'ace': 14
}

__gin_ranks = {
    'ace': 1, 'two': 2, 'three': 3, 'four': 4, 'five': 5, 'six': 6, 'seven': 7, 'eight': 8,
    'nine': 9, 'ten': 10, 'jack': 11, 'queen': 12, 'king': 13,
}

__gin_ranks_r = {__gin_ranks[r]: r for r in __gin_ranks}

__bridge_deck = [(rank, suit) for suit in __suits for rank in __bridge_ranks.keys()]

__gin_deck = [(rank, suit) for suit in __suits for rank in __gin_ranks.keys()]


def count_deadwood_generator(seed):
    rng = Random(seed)
    for _ in range(10000):
        hand = []
        rank = rng.randint(1, 13)
        suit = rng.choice(__suits)
        while len(hand) < 10:
            if (rank, suit) not in hand:
                hand.append((rank, suit))
            roll = rng.randint(0, 99)
            if roll < 40:
                suit = rng.choice(__suits)
            elif roll < 80:
                rank = max(min(rank + rng.choice([-1, 1]), 13), 1)
            else:
                rank = rng.randint(1, 13)
                suit = rng.choice(__suits)
        hand.sort()
        hand = [(__gin_ranks_r[rank], suit) for (rank, suit) in hand]
        yield hand,


def count_sevens_generator(seed):
    chosen = [4, 7, 10, 17, 46, 47, 78, 199, 206, 207, 776, 777, 778, 6999, 7000, 7001, 7776, 7777, 7778]
    yield from ((n,) for n in chosen)
    for n in islice(scale_random(seed, 3, 5), 1500):
        yield n,


__morse = {
    '.-': 'a', '-...': 'b', '-.-.': 'c', '-..': 'd', '.': 'e', '..-.': 'f', '--.': 'g', '....': 'h',
    '..': 'i', '.---': 'j', '-.-': 'k', '.-..': 'l', '--': 'm', '-.': 'n', '---': 'o', '.--.': 'p',
    '--.-': 'q', '.-.': 'r', '...': 's', '-': 't', '..-': 'u', '...-': 'v', '.--': 'w', '-..-': 'x',
    '-.--': 'y', '--..': 'z'
}

__morse_r = {__morse[k]: k for k in __morse}


def count_morse_generator(seed):
    for letters in ["omg", "whoa", "etaoinshrdlu", "abcdefghijklmnopqrstuvwxyz"]:
        yield "".join([__morse_r[c] for c in letters]), letters
    rng = Random(seed)
    for n in islice(pyramid(3, 5, 7), 500):
        letters = "".join(rng.sample("abcdefghijklmnopqrstuvwxyz", n))
        message = "".join([__morse_r[c] for c in letters])
        yield message, letters


def othello_moves_generator(seed):
    rng = Random(seed)
    dirs = [(0, 1), (1, 0), (0, -1), (-1, 0)]
    for pn in islice(pyramid(5, 3, 4), 2000):
        othello, desdemona = [(3, 3), (4, 4)], [(3, 4), (4, 3)]
        taken = set(othello + desdemona)
        while len(taken) < pn:
            (x, y) = rng.choice(othello if rng.randint(0, 99) < 50 else desdemona)
            dx, dy = rng.choice(dirs)
            nx, ny = x + dx, y + dy
            if 0 <= nx < 8 and 0 < ny < 8 and (nx, ny) not in taken:
                taken.add((nx, ny))
                (othello if rng.randint(0, 99) < 50 else desdemona).append((nx, ny))
        yield othello, desdemona


# Knuth and Liang's original hyphenation patterns from classic TeX. In public domain.

__liang_patterns = """
.ach4 .ad4der .af1t .al3t .am5at .an5c .ang4 .ani5m .ant4 .an3te .anti5s .ar5s
.ar4tie .ar4ty .as3c .as1p .as1s .aster5 .atom5 .au1d .av4i .awn4 .ba4g .ba5na
.bas4e .ber4 .be5ra .be3sm .be5sto .bri2 .but4ti .cam4pe .can5c .capa5b .car5ol
.ca4t .ce4la .ch4 .chill5i .ci2 .cit5r .co3e .co4r .cor5ner .de4moi .de3o .de3ra
.de3ri .des4c .dictio5 .do4t .du4c .dumb5 .earth5 .eas3i .eb4 .eer4 .eg2 .el5d
.el3em .enam3 .en3g .en3s .eq5ui5t .er4ri .es3 .eu3 .eye5 .fes3 .for5mer .ga2
.ge2 .gen3t4 .ge5og .gi5a .gi4b .go4r .hand5i .han5k .he2 .hero5i .hes3 .het3
.hi3b .hi3er .hon5ey .hon3o .hov5 .id4l .idol3 .im3m .im5pin .in1 .in3ci .ine2
.in2k .in3s .ir5r .is4i .ju3r .la4cy .la4m .lat5er .lath5 .le2 .leg5e .len4
.lep5 .lev1 .li4g .lig5a .li2n .li3o .li4t .mag5a5 .mal5o .man5a .mar5ti .me2
.mer3c .me5ter .mis1 .mist5i .mon3e .mo3ro .mu5ta .muta5b .ni4c .od2 .odd5
.of5te .or5ato .or3c .or1d .or3t .os3 .os4tl .oth3 .out3 .ped5al .pe5te .pe5tit
.pi4e .pio5n .pi2t .pre3m .ra4c .ran4t .ratio5na .ree2 .re5mit .res2 .re5stat
.ri4g .rit5u .ro4q .ros5t .row5d .ru4d .sci3e .self5 .sell5 .se2n .se5rie .sh2
.si2 .sing4 .st4 .sta5bl .sy2 .ta4 .te4 .ten5an .th2 .ti2 .til4 .tim5o5 .ting4
.tin5k .ton4a .to4p .top5i .tou5s .trib5ut .un1a .un3ce .under5 .un1e .un5k
.un5o .un3u .up3 .ure3 .us5a .ven4de .ve5ra .wil5i .ye4 4ab. a5bal a5ban abe2
ab5erd abi5a ab5it5ab ab5lat ab5o5liz 4abr ab5rog ab3ul a4car ac5ard ac5aro
a5ceou ac1er a5chet 4a2ci a3cie ac1in a3cio ac5rob act5if ac3ul ac4um a2d ad4din
ad5er. 2adi a3dia ad3ica adi4er a3dio a3dit a5diu ad4le ad3ow ad5ran ad4su 4adu
a3duc ad5um ae4r aeri4e a2f aff4 a4gab aga4n ag5ell age4o 4ageu ag1i 4ag4l ag1n
a2go 3agog ag3oni a5guer ag5ul a4gy a3ha a3he ah4l a3ho ai2 a5ia a3ic. ai5ly
a4i4n ain5in ain5o ait5en a1j ak1en al5ab al3ad a4lar 4aldi 2ale al3end a4lenti
a5le5o al1i al4ia. ali4e al5lev 4allic 4alm a5log. a4ly. 4alys 5a5lyst 5alyt
3alyz 4ama am5ab am3ag ama5ra am5asc a4matis a4m5ato am5era am3ic am5if am5ily
am1in ami4no a2mo a5mon amor5i amp5en a2n an3age 3analy a3nar an3arc anar4i
a3nati 4and ande4s an3dis an1dl an4dow a5nee a3nen an5est. a3neu 2ang ang5ie
an1gl a4n1ic a3nies an3i3f an4ime a5nimi a5nine an3io a3nip an3ish an3it a3niu
an4kli 5anniz ano4 an5ot anoth5 an2sa an4sco an4sn an2sp ans3po an4st an4sur
antal4 an4tie 4anto an2tr an4tw an3ua an3ul a5nur 4ao apar4 ap5at ap5ero a3pher
4aphi a4pilla ap5illar ap3in ap3ita a3pitu a2pl apoc5 ap5ola apor5i apos3t
aps5es a3pu aque5 2a2r ar3act a5rade ar5adis ar3al a5ramete aran4g ara3p ar4at
a5ratio ar5ativ a5rau ar5av4 araw4 arbal4 ar4chan ar5dine ar4dr ar5eas a3ree
ar3ent a5ress ar4fi ar4fl ar1i ar5ial ar3ian a3riet ar4im ar5inat ar3io ar2iz
ar2mi ar5o5d a5roni a3roo ar2p ar3q arre4 ar4sa ar2sh 4as. as4ab as3ant ashi4
a5sia. a3sib a3sic 5a5si4t ask3i as4l a4soc as5ph as4sh as3ten as1tr asur5a a2ta
at3abl at5ac at3alo at5ap ate5c at5ech at3ego at3en. at3era ater5n a5terna
at3est at5ev 4ath ath5em a5then at4ho ath5om 4ati. a5tia at5i5b at1ic at3if
ation5ar at3itu a4tog a2tom at5omiz a4top a4tos a1tr at5rop at4sk at4tag at5te
at4th a2tu at5ua at5ue at3ul at3ura a2ty au4b augh3 au3gu au4l2 aun5d au3r
au5sib aut5en au1th a2va av3ag a5van ave4no av3era av5ern av5ery av1i avi4er
av3ig av5oc a1vor 3away aw3i aw4ly aws4 ax4ic ax4id ay5al aye4 ays4 azi4er azz5i
5ba. bad5ger ba4ge bal1a ban5dag ban4e ban3i barbi5 bari4a bas4si 1bat ba4z 2b1b
b2be b3ber bbi4na 4b1d 4be. beak4 beat3 4be2d be3da be3de be3di be3gi be5gu 1bel
be1li be3lo 4be5m be5nig be5nu 4bes4 be3sp be5str 3bet bet5iz be5tr be3tw be3w
be5yo 2bf 4b3h bi2b bi4d 3bie bi5en bi4er 2b3if 1bil bi3liz bina5r4 bin4d bi5net
bi3ogr bi5ou bi2t 3bi3tio bi3tr 3bit5ua b5itz b1j bk4 b2l2 blath5 b4le. blen4
5blesp b3lis b4lo blun4t 4b1m 4b3n bne5g 3bod bod3i bo4e bol3ic bom4bi bon4a
bon5at 3boo 5bor. 4b1ora bor5d 5bore 5bori 5bos4 b5ota both5 bo4to bound3 4bp
4brit broth3 2b5s2 bsor4 2bt bt4l b4to b3tr buf4fer bu4ga bu3li bumi4 bu4n
bunt4i bu3re bus5ie buss4e 5bust 4buta 3butio b5uto b1v 4b5w 5by. bys4 1ca
cab3in ca1bl cach4 ca5den 4cag4 2c5ah ca3lat cal4la call5in 4calo can5d can4e
can4ic can5is can3iz can4ty cany4 ca5per car5om cast5er cas5tig 4casy ca4th
4cativ cav5al c3c ccha5 cci4a ccompa5 ccon4 ccou3t 2ce. 4ced. 4ceden 3cei 5cel.
3cell 1cen 3cenc 2cen4e 4ceni 3cent 3cep ce5ram 4cesa 3cessi ces5si5b ces5t cet4
c5e4ta cew4 2ch 4ch. 4ch3ab 5chanic ch5a5nis che2 cheap3 4ched che5lo 3chemi
ch5ene ch3er. ch3ers 4ch1in 5chine. ch5iness 5chini 5chio 3chit chi2z 3cho2
ch4ti 1ci 3cia ci2a5b cia5r ci5c 4cier 5cific. 4cii ci4la 3cili 2cim 2cin c4ina
3cinat cin3em c1ing c5ing. 5cino cion4 4cipe ci3ph 4cipic 4cista 4cisti 2c1it
cit3iz 5ciz ck1 ck3i 1c4l4 4clar c5laratio 5clare cle4m 4clic clim4 cly4 c5n 1co
co5ag coe2 2cog co4gr coi4 co3inc col5i 5colo col3or com5er con4a c4one con3g
con5t co3pa cop3ic co4pl 4corb coro3n cos4e cov1 cove4 cow5a coz5e co5zi c1q
cras5t 5crat. 5cratic cre3at 5cred 4c3reta cre4v cri2 cri5f c4rin cris4 5criti
cro4pl crop5o cros4e cru4d 4c3s2 2c1t cta4b ct5ang c5tant c2te c3ter c4ticu
ctim3i ctu4r c4tw cud5 c4uf c4ui cu5ity 5culi cul4tis 3cultu cu2ma c3ume cu4mi
3cun cu3pi cu5py cur5a4b cu5ria 1cus cuss4i 3c4ut cu4tie 4c5utiv 4cutr 1cy cze4
1d2a 5da. 2d3a4b dach4 4daf 2dag da2m2 dan3g dard5 dark5 4dary 3dat 4dativ 4dato
5dav4 dav5e 5day d1b d5c d1d4 2de. deaf5 deb5it de4bon decan4 de4cil de5com
2d1ed 4dee. de5if deli4e del5i5q de5lo d4em 5dem. 3demic dem5ic. de5mil de4mons
demor5 1den de4nar de3no denti5f de3nu de1p de3pa depi4 de2pu d3eq d4erh 5derm
dern5iz der5s des2 d2es. de1sc de2s5o des3ti de3str de4su de1t de2to de1v dev3il
4dey 4d1f d4ga d3ge4t dg1i d2gy d1h2 5di. 1d4i3a dia5b di4cam d4ice 3dict 3did
5di3en d1if di3ge di4lato d1in 1dina 3dine. 5dini di5niz 1dio dio5g di4pl dir2
di1re dirt5i dis1 5disi d4is3t d2iti 1di1v d1j d5k2 4d5la 3dle. 3dled 3dles.
4dless 2d3lo 4d5lu 2dly d1m 4d1n4 1do 3do. do5de 5doe 2d5of d4og do4la doli4
do5lor dom5iz do3nat doni4 doo3d dop4p d4or 3dos 4d5out do4v 3dox d1p 1dr
drag5on 4drai dre4 drea5r 5dren dri4b dril4 dro4p 4drow 5drupli 4dry 2d1s2 ds4p
d4sw d4sy d2th 1du d1u1a du2c d1uca duc5er 4duct. 4ducts du5el du4g d3ule dum4be
du4n 4dup du4pe d1v d1w d2y 5dyn dy4se dys5p e1a4b e3act ead1 ead5ie ea4ge
ea5ger ea4l eal5er eal3ou eam3er e5and ear3a ear4c ear5es ear4ic ear4il ear5k
ear2t eart3e ea5sp e3ass east3 ea2t eat5en eath3i e5atif e4a3tu ea2v eav3en
eav5i eav5o 2e1b e4bel. e4bels e4ben e4bit e3br e4cad ecan5c ecca5 e1ce ec5essa
ec2i e4cib ec5ificat ec5ifie ec5ify ec3im eci4t e5cite e4clam e4clus e2col
e4comm e4compe e4conc e2cor ec3ora eco5ro e1cr e4crem ec4tan ec4te e1cu e4cul
ec3ula 2e2da 4ed3d e4d1er ede4s 4edi e3dia ed3ib ed3ica ed3im ed1it edi5z 4edo
e4dol edon2 e4dri e4dul ed5ulo ee2c eed3i ee2f eel3i ee4ly ee2m ee4na ee4p1
ee2s4 eest4 ee4ty e5ex e1f e4f3ere 1eff e4fic 5efici efil4 e3fine ef5i5nite
3efit efor5es e4fuse. 4egal eger4 eg5ib eg4ic eg5ing e5git5 eg5n e4go. e4gos
eg1ul e5gur 5egy e1h4 eher4 ei2 e5ic ei5d eig2 ei5gl e3imb e3inf e1ing e5inst
eir4d eit3e ei3th e5ity e1j e4jud ej5udi eki4n ek4la e1la e4la. e4lac elan4d
el5ativ e4law elaxa4 e3lea el5ebra 5elec e4led el3ega e5len e4l1er e1les el2f
el2i e3libe e4l5ic. el3ica e3lier el5igib e5lim e4l3ing e3lio e2lis el5ish
e3liv3 4ella el4lab ello4 e5loc el5og el3op. el2sh el4ta e5lud el5ug e4mac e4mag
e5man em5ana em5b e1me e2mel e4met em3ica emi4e em5igra em1in2 em5ine em3i3ni
e4mis em5ish e5miss em3iz 5emniz emo4g emoni5o em3pi e4mul em5ula emu3n e3my
en5amo e4nant ench4er en3dic e5nea e5nee en3em en5ero en5esi en5est en3etr e3new
en5ics e5nie e5nil e3nio en3ish en3it e5niu 5eniz 4enn 4eno eno4g e4nos en3ov
en4sw ent5age 4enthes en3ua en5uf e3ny. 4en3z e5of eo2g e4oi4 e3ol eop3ar e1or
eo3re eo5rol eos4 e4ot eo4to e5out e5ow e2pa e3pai ep5anc e5pel e3pent ep5etitio
ephe4 e4pli e1po e4prec ep5reca e4pred ep3reh e3pro e4prob ep4sh ep5ti5b e4put
ep5uta e1q equi3l e4q3ui3s er1a era4b 4erand er3ar 4erati. 2erb er4bl er3ch
er4che 2ere. e3real ere5co ere3in er5el. er3emo er5ena er5ence 4erene er3ent
ere4q er5ess er3est eret4 er1h er1i e1ria4 5erick e3rien eri4er er3ine e1rio
4erit er4iu eri4v e4riva er3m4 er4nis 4ernit 5erniz er3no 2ero er5ob e5roc ero4r
er1ou er1s er3set ert3er 4ertl er3tw 4eru eru4t 5erwau e1s4a e4sage. e4sages
es2c e2sca es5can e3scr es5cu e1s2e e2sec es5ecr es5enc e4sert. e4serts e4serva
4esh e3sha esh5en e1si e2sic e2sid es5iden es5igna e2s5im es4i4n esis4te esi4u
e5skin es4mi e2sol es3olu e2son es5ona e1sp es3per es5pira es4pre 2ess es4si4b
estan4 es3tig es5tim 4es2to e3ston 2estr e5stro estruc5 e2sur es5urr es4w eta4b
eten4d e3teo ethod3 et1ic e5tide etin4 eti4no e5tir e5titio et5itiv 4etn et5ona
e3tra e3tre et3ric et5rif et3rog et5ros et3ua et5ym et5z 4eu e5un e3up eu3ro
eus4 eute4 euti5l eu5tr eva2p5 e2vas ev5ast e5vea ev3ell evel3o e5veng even4i
ev1er e5verb e1vi ev3id evi4l e4vin evi4v e5voc e5vu e1wa e4wag e5wee e3wh ewil5
ew3ing e3wit 1exp 5eyc 5eye. eys4 1fa fa3bl fab3r fa4ce 4fag fain4 fall5e 4fa4ma
fam5is 5far far5th fa3ta fa3the 4fato fault5 4f5b 4fd 4fe. feas4 feath3 fe4b
4feca 5fect 2fed fe3li fe4mo fen2d fend5e fer1 5ferr fev4 4f1f f4fes f4fie
f5fin. f2f5is f4fly f2fy 4fh 1fi fi3a 2f3ic. 4f3ical f3ican 4ficate f3icen
fi3cer fic4i 5ficia 5ficie 4fics fi3cu fi5del fight5 fil5i fill5in 4fily 2fin
5fina fin2d5 fi2ne f1in3g fin4n fis4ti f4l2 f5less flin4 flo3re f2ly5 4fm 4fn
1fo 5fon fon4de fon4t fo2r fo5rat for5ay fore5t for4i fort5a fos5 4f5p fra4t
f5rea fres5c fri2 fril4 frol5 2f3s 2ft f4to f2ty 3fu fu5el 4fug fu4min fu5ne
fu3ri fusi4 fus4s 4futa 1fy 1ga gaf4 5gal. 3gali ga3lo 2gam ga5met g5amo gan5is
ga3niz gani5za 4gano gar5n4 gass4 gath3 4gativ 4gaz g3b gd4 2ge. 2ged geez4
gel4in ge5lis ge5liz 4gely 1gen ge4nat ge5niz 4geno 4geny 1geo ge3om g4ery 5gesi
geth5 4geto ge4ty ge4v 4g1g2 g2ge g3ger gglu5 ggo4 gh3in gh5out gh4to 5gi. 1gi4a
gia5r g1ic 5gicia g4ico gien5 5gies. gil4 g3imen 3g4in. gin5ge 5g4ins 5gio 3gir
gir4l g3isl gi4u 5giv 3giz gl2 gla4 glad5i 5glas 1gle gli4b g3lig 3glo glo3r g1m
g4my gn4a g4na. gnet4t g1ni g2nin g4nio g1no g4non 1go 3go. gob5 5goe 3g4o4g
go3is gon2 4g3o3na gondo5 go3ni 5goo go5riz gor5ou 5gos. gov1 g3p 1gr 4grada
g4rai gran2 5graph. g5rapher 5graphic 4graphy 4gray gre4n 4gress. 4grit g4ro
gruf4 gs2 g5ste gth3 gu4a 3guard 2gue 5gui5t 3gun 3gus 4gu4t g3w 1gy 2g5y3n
gy5ra h3ab4l hach4 hae4m hae4t h5agu ha3la hala3m ha4m han4ci han4cy 5hand.
han4g hang5er hang5o h5a5niz han4k han4te hap3l hap5t ha3ran ha5ras har2d hard3e
har4le harp5en har5ter has5s haun4 5haz haz3a h1b 1head 3hear he4can h5ecat h4ed
he5do5 he3l4i hel4lis hel4ly h5elo hem4p he2n hena4 hen5at heo5r hep5 h4era
hera3p her4ba here5a h3ern h5erou h3ery h1es he2s5p he4t het4ed heu4 h1f h1h
hi5an hi4co high5 h4il2 himer4 h4ina hion4e hi4p hir4l hi3ro hir4p hir4r his3el
his4s hith5er hi2v 4hk 4h1l4 hlan4 h2lo hlo3ri 4h1m hmet4 2h1n h5odiz h5ods ho4g
hoge4 hol5ar 3hol4e ho4ma home3 hon4a ho5ny 3hood hoon4 hor5at ho5ris hort3e
ho5ru hos4e ho5sen hos1p 1hous house3 hov5el 4h5p 4hr4 hree5 hro5niz hro3po
4h1s2 h4sh h4tar ht1en ht5es h4ty hu4g hu4min hun5ke hun4t hus3t4 hu4t h1w
h4wart hy3pe hy3ph hy2s 2i1a i2al iam4 iam5ete i2an 4ianc ian3i 4ian4t ia5pe
iass4 i4ativ ia4tric i4atu ibe4 ib3era ib5ert ib5ia ib3in ib5it. ib5ite i1bl
ib3li i5bo i1br i2b5ri i5bun 4icam 5icap 4icar i4car. i4cara icas5 i4cay iccu4
4iceo 4ich 2ici i5cid ic5ina i2cip ic3ipa i4cly i2c5oc 4i1cr 5icra i4cry ic4te
ictu2 ic4t3ua ic3ula ic4um ic5uo i3cur 2id i4dai id5anc id5d ide3al ide4s i2di
id5ian idi4ar i5die id3io idi5ou id1it id5iu i3dle i4dom id3ow i4dr i2du id5uo
2ie4 ied4e 5ie5ga ield3 ien5a4 ien4e i5enn i3enti i1er. i3esc i1est i3et 4if.
if5ero iff5en if4fr 4ific. i3fie i3fl 4ift 2ig iga5b ig3era ight3i 4igi i3gib
ig3il ig3in ig3it i4g4l i2go ig3or ig5ot i5gre igu5i ig1ur i3h 4i5i4 i3j 4ik
i1la il3a4b i4lade i2l5am ila5ra i3leg il1er ilev4 il5f il1i il3ia il2ib il3io
il4ist 2ilit il2iz ill5ab 4iln il3oq il4ty il5ur il3v i4mag im3age ima5ry
imenta5r 4imet im1i im5ida imi5le i5mini 4imit im4ni i3mon i2mu im3ula 2in.
i4n3au 4inav incel4 in3cer 4ind in5dling 2ine i3nee iner4ar i5ness 4inga 4inge
in5gen 4ingi in5gling 4ingo 4ingu 2ini i5ni. i4nia in3io in1is i5nite. 5initio
in3ity 4ink 4inl 2inn 2i1no i4no4c ino4s i4not 2ins in3se insur5a 2int. 2in4th
in1u i5nus 4iny 2io 4io. ioge4 io2gr i1ol io4m ion3at ion4ery ion3i io5ph ior3i
i4os io5th i5oti io4to i4our 2ip ipe4 iphras4 ip3i ip4ic ip4re4 ip3ul i3qua
iq5uef iq3uid iq3ui3t 4ir i1ra ira4b i4rac ird5e ire4de i4ref i4rel4 i4res ir5gi
ir1i iri5de ir4is iri3tu 5i5r2iz ir4min iro4g 5iron. ir5ul 2is. is5ag is3ar
isas5 2is1c is3ch 4ise is3er 3isf is5han is3hon ish5op is3ib isi4d i5sis is5itiv
4is4k islan4 4isms i2so iso5mer is1p is2pi is4py 4is1s is4sal issen4 is4ses
is4ta. is1te is1ti ist4ly 4istral i2su is5us 4ita. ita4bi i4tag 4ita5m i3tan
i3tat 2ite it3era i5teri it4es 2ith i1ti 4itia 4i2tic it3ica 5i5tick it3ig
it5ill i2tim 2itio 4itis i4tism i2t5o5m 4iton i4tram it5ry 4itt it3uat i5tud
it3ul 4itz. i1u 2iv iv3ell iv3en. i4v3er. i4vers. iv5il. iv5io iv1it i5vore
iv3o3ro i4v3ot 4i5w ix4o 4iy 4izar izi4 5izont 5ja jac4q ja4p 1je jer5s 4jestie
4jesty jew3 jo4p 5judg 3ka. k3ab k5ag kais4 kal4 k1b k2ed 1kee ke4g ke5li k3en4d
k1er kes4 k3est. ke4ty k3f kh4 k1i 5ki. 5k2ic k4ill kilo5 k4im k4in. kin4de
k5iness kin4g ki4p kis4 k5ish kk4 k1l 4kley 4kly k1m k5nes 1k2no ko5r kosh4 k3ou
kro5n 4k1s2 k4sc ks4l k4sy k5t k1w lab3ic l4abo laci4 l4ade la3dy lag4n lam3o
3land lan4dl lan5et lan4te lar4g lar3i las4e la5tan 4lateli 4lativ 4lav la4v4a
2l1b lbin4 4l1c2 lce4 l3ci 2ld l2de ld4ere ld4eri ldi4 ld5is l3dr l4dri le2a
le4bi left5 5leg. 5legg le4mat lem5atic 4len. 3lenc 5lene. 1lent le3ph le4pr
lera5b ler4e 3lerg 3l4eri l4ero les2 le5sco 5lesq 3less 5less. l3eva lev4er.
lev4era lev4ers 3ley 4leye 2lf l5fr 4l1g4 l5ga lgar3 l4ges lgo3 2l3h li4ag li2am
liar5iz li4as li4ato li5bi 5licio li4cor 4lics 4lict. l4icu l3icy l3ida lid5er
3lidi lif3er l4iff li4fl 5ligate 3ligh li4gra 3lik 4l4i4l lim4bl lim3i li4mo
l4im4p l4ina 1l4ine lin3ea lin3i link5er li5og 4l4iq lis4p l1it l2it. 5litica
l5i5tics liv3er l1iz 4lj lka3 l3kal lka4t l1l l4law l2le l5lea l3lec l3leg l3lel
l3le4n l3le4t ll2i l2lin4 l5lina ll4o lloqui5 ll5out l5low 2lm l5met lm3ing
l4mod lmon4 2l1n2 3lo. lob5al lo4ci 4lof 3logic l5ogo 3logu lom3er 5long lon4i
l3o3niz lood5 5lope. lop3i l3opm lora4 lo4rato lo5rie lor5ou 5los. los5et
5losophiz 5losophy los4t lo4ta loun5d 2lout 4lov 2lp lpa5b l3pha l5phi lp5ing
l3pit l4pl l5pr 4l1r 2l1s2 l4sc l2se l4sie 4lt lt5ag ltane5 l1te lten4 ltera4
lth3i l5ties. ltis4 l1tr ltu2 ltur3a lu5a lu3br luch4 lu3ci lu3en luf4 lu5id
lu4ma 5lumi l5umn. 5lumnia lu3o luo3r 4lup luss4 lus3te 1lut l5ven l5vet4 2l1w
1ly 4lya 4lyb ly5me ly3no 2lys4 l5yse 1ma 2mab ma2ca ma5chine ma4cl mag5in 5magn
2mah maid5 4mald ma3lig ma5lin mal4li mal4ty 5mania man5is man3iz 4map ma5rine.
ma5riz mar4ly mar3v ma5sce mas4e mas1t 5mate math3 ma3tis 4matiza 4m1b mba4t5
m5bil m4b3ing mbi4v 4m5c 4me. 2med 4med. 5media me3die m5e5dy me2g mel5on mel4t
me2m mem1o3 1men men4a men5ac men4de 4mene men4i mens4 mensu5 3ment men4te me5on
m5ersa 2mes 3mesti me4ta met3al me1te me5thi m4etr 5metric me5trie me3try me4v
4m1f 2mh 5mi. mi3a mid4a mid4g mig4 3milia m5i5lie m4ill min4a 3mind m5inee
m4ingl min5gli m5ingly min4t m4inu miot4 m2is mis4er. mis5l mis4ti m5istry 4mith
m2iz 4mk 4m1l m1m mma5ry 4m1n mn4a m4nin mn4o 1mo 4mocr 5mocratiz mo2d1 mo4go
mois2 moi5se 4mok mo5lest mo3me mon5et mon5ge moni3a mon4ism mon4ist mo3niz
monol4 mo3ny. mo2r 4mora. mos2 mo5sey mo3sp moth3 m5ouf 3mous mo2v 4m1p mpara5
mpa5rab mpar5i m3pet mphas4 m2pi mpi4a mp5ies m4p1in m5pir mp5is mpo3ri mpos5ite
m4pous mpov5 mp4tr m2py 4m3r 4m1s2 m4sh m5si 4mt 1mu mula5r4 5mult multi3 3mum
mun2 4mup mu4u 4mw 1na 2n1a2b n4abu 4nac. na4ca n5act nag5er. nak4 na4li na5lia
4nalt na5mit n2an nanci4 nan4it nank4 nar3c 4nare nar3i nar4l n5arm n4as nas4c
nas5ti n2at na3tal nato5miz n2au nau3se 3naut nav4e 4n1b4 ncar5 n4ces. n3cha
n5cheo n5chil n3chis nc1in nc4it ncour5a n1cr n1cu n4dai n5dan n1de nd5est.
ndi4b n5d2if n1dit n3diz n5duc ndu4r nd2we 2ne. n3ear ne2b neb3u ne2c 5neck 2ned
ne4gat neg5ativ 5nege ne4la nel5iz ne5mi ne4mo 1nen 4nene 3neo ne4po ne2q n1er
nera5b n4erar n2ere n4er5i ner4r 1nes 2nes. 4nesp 2nest 4nesw 3netic ne4v n5eve
ne4w n3f n4gab n3gel nge4n4e n5gere n3geri ng5ha n3gib ng1in n5git n4gla ngov4
ng5sh n1gu n4gum n2gy 4n1h4 nha4 nhab3 nhe4 3n4ia ni3an ni4ap ni3ba ni4bl ni4d
ni5di ni4er ni2fi ni5ficat n5igr nik4 n1im ni3miz n1in 5nine. nin4g ni4o 5nis.
nis4ta n2it n4ith 3nitio n3itor ni3tr n1j 4nk2 n5kero n3ket nk3in n1kl 4n1l n5m
nme4 nmet4 4n1n2 nne4 nni3al nni4v nob4l no3ble n5ocl 4n3o2d 3noe 4nog noge4
nois5i no5l4i 5nologis 3nomic n5o5miz no4mo no3my no4n non4ag non5i n5oniz 4nop
5nop5o5li nor5ab no4rary 4nosc nos4e nos5t no5ta 1nou 3noun nov3el3 nowl3 n1p4
npi4 npre4c n1q n1r nru4 2n1s2 ns5ab nsati4 ns4c n2se n4s3es nsid1 nsig4 n2sl
ns3m n4soc ns4pe n5spi nsta5bl n1t nta4b nter3s nt2i n5tib nti4er nti2f n3tine
n4t3ing nti4p ntrol5li nt4s ntu3me nu1a nu4d nu5en nuf4fe n3uin 3nu3it n4um
nu1me n5umi 3nu4n n3uo nu3tr n1v2 n1w4 nym4 nyp4 4nz n3za 4oa oad3 o5a5les oard3
oas4e oast5e oat5i ob3a3b o5bar obe4l o1bi o2bin ob5ing o3br ob3ul o1ce och4
o3chet ocif3 o4cil o4clam o4cod oc3rac oc5ratiz ocre3 5ocrit octor5a oc3ula
o5cure od5ded od3ic odi3o o2do4 odor3 od5uct. od5ucts o4el o5eng o3er oe4ta o3ev
o2fi of5ite ofit4t o2g5a5r og5ativ o4gato o1ge o5gene o5geo o4ger o3gie 1o1gis
og3it o4gl o5g2ly 3ogniz o4gro ogu5i 1ogy 2ogyn o1h2 ohab5 oi2 oic3es oi3der
oiff4 oig4 oi5let o3ing oint5er o5ism oi5son oist5en oi3ter o5j 2ok o3ken ok5ie
o1la o4lan olass4 ol2d old1e ol3er o3lesc o3let ol4fi ol2i o3lia o3lice ol5id.
o3li4f o5lil ol3ing o5lio o5lis. ol3ish o5lite o5litio o5liv olli4e ol5ogiz
olo4r ol5pl ol2t ol3ub ol3ume ol3un o5lus ol2v o2ly om5ah oma5l om5atiz om2be
om4bl o2me om3ena om5erse o4met om5etry o3mia om3ic. om3ica o5mid om1in o5mini
5ommend omo4ge o4mon om3pi ompro5 o2n on1a on4ac o3nan on1c 3oncil 2ond on5do
o3nen on5est on4gu on1ic o3nio on1is o5niu on3key on4odi on3omy on3s onspi4
onspir5a onsu4 onten4 on3t4i ontif5 on5um onva5 oo2 ood5e ood5i oo4k oop3i o3ord
oost5 o2pa ope5d op1er 3opera 4operag 2oph o5phan o5pher op3ing o3pit o5pon
o4posi o1pr op1u opy5 o1q o1ra o5ra. o4r3ag or5aliz or5ange ore5a o5real or3ei
ore5sh or5est. orew4 or4gu 4o5ria or3ica o5ril or1in o1rio or3ity o3riu or2mi
orn2e o5rof or3oug or5pe 3orrh or4se ors5en orst4 or3thi or3thy or4ty o5rum o1ry
os3al os2c os4ce o3scop 4oscopi o5scr os4i4e os5itiv os3ito os3ity osi4u os4l
o2so os4pa os4po os2ta o5stati os5til os5tit o4tan otele4g ot3er. ot5ers o4tes
4oth oth5esi oth3i4 ot3ic. ot5ica o3tice o3tif o3tis oto5s ou2 ou3bl ouch5i
ou5et ou4l ounc5er oun2d ou5v ov4en over4ne over3s ov4ert o3vis oviti4 o5v4ol
ow3der ow3el ow5est ow1i own5i o4wo oy1a 1pa pa4ca pa4ce pac4t p4ad 5pagan
p3agat p4ai pain4 p4al pan4a pan3el pan4ty pa3ny pa1p pa4pu para5bl par5age
par5di 3pare par5el p4a4ri par4is pa2te pa5ter 5pathic pa5thy pa4tric pav4 3pay
4p1b pd4 4pe. 3pe4a pear4l pe2c 2p2ed 3pede 3pedi pedia4 ped4ic p4ee pee4d pek4
pe4la peli4e pe4nan p4enc pen4th pe5on p4era. pera5bl p4erag p4eri peri5st
per4mal perme5 p4ern per3o per3ti pe5ru per1v pe2t pe5ten pe5tiz 4pf 4pg 4ph.
phar5i phe3no ph4er ph4es. ph1ic 5phie ph5ing 5phisti 3phiz ph2l 3phob 3phone
5phoni pho4r 4phs ph3t 5phu 1phy pi3a pian4 pi4cie pi4cy p4id p5ida pi3de 5pidi
3piec pi3en pi4grap pi3lo pi2n p4in. pind4 p4ino 3pi1o pion4 p3ith pi5tha pi2tu
2p3k2 1p2l2 3plan plas5t pli3a pli5er 4plig pli4n ploi4 plu4m plum4b 4p1m 2p3n
po4c 5pod. po5em po3et5 5po4g poin2 5point poly5t po4ni po4p 1p4or po4ry 1pos
pos1s p4ot po4ta 5poun 4p1p ppa5ra p2pe p4ped p5pel p3pen p3per p3pet ppo5site
pr2 pray4e 5preci pre5co pre3em pref5ac pre4la pre3r p3rese 3press pre5ten pre3v
5pri4e prin4t3 pri4s pris3o p3roca prof5it pro3l pros3e pro1t 2p1s2 p2se ps4h
p4sib 2p1t pt5a4b p2te p2th pti3m ptu4r p4tw pub3 pue4 puf4 pul3c pu4m pu2n
pur4r 5pus pu2t 5pute put3er pu3tr put4ted put4tin p3w qu2 qua5v 2que. 3quer
3quet 2rab ra3bi rach4e r5acl raf5fi raf4t r2ai ra4lo ram3et r2ami rane5o ran4ge
r4ani ra5no rap3er 3raphy rar5c rare4 rar5ef 4raril r2as ration4 rau4t ra5vai
rav3el ra5zie r1b r4bab r4bag rbi2 rbi4f r2bin r5bine rb5ing. rb4o r1c r2ce
rcen4 r3cha rch4er r4ci4b rc4it rcum3 r4dal rd2i rdi4a rdi4er rdin4 rd3ing 2re.
re1al re3an re5arr 5reav re4aw r5ebrat rec5oll rec5ompe re4cre 2r2ed re1de
re3dis red5it re4fac re2fe re5fer. re3fi re4fy reg3is re5it re1li re5lu r4en4ta
ren4te re1o re5pin re4posi re1pu r1er4 r4eri rero4 re5ru r4es. re4spi ress5ib
res2t re5stal re3str re4ter re4ti4z re3tri reu2 re5uti rev2 re4val rev3el
r5ev5er. re5vers re5vert re5vil rev5olu re4wh r1f rfu4 r4fy rg2 rg3er r3get
r3gic rgi4n rg3ing r5gis r5git r1gl rgo4n r3gu rh4 4rh. 4rhal ri3a ria4b ri4ag
r4ib rib3a ric5as r4ice 4rici 5ricid ri4cie r4ico rid5er ri3enc ri3ent ri1er
ri5et rig5an 5rigi ril3iz 5riman rim5i 3rimo rim4pe r2ina 5rina. rin4d rin4e
rin4g ri1o 5riph riph5e ri2pl rip5lic r4iq r2is r4is. ris4c r3ish ris4p ri3ta3b
r5ited. rit5er. rit5ers rit3ic ri2tu rit5ur riv5el riv3et riv3i r3j r3ket rk4le
rk4lin r1l rle4 r2led r4lig r4lis rl5ish r3lo4 r1m rma5c r2me r3men rm5ers
rm3ing r4ming. r4mio r3mit r4my r4nar r3nel r4ner r5net r3ney r5nic r1nis4 r3nit
r3niv rno4 r4nou r3nu rob3l r2oc ro3cr ro4e ro1fe ro5fil rok2 ro5ker 5role.
rom5ete rom4i rom4p ron4al ron4e ro5n4is ron4ta 1room 5root ro3pel rop3ic ror3i
ro5ro ros5per ros4s ro4the ro4ty ro4va rov5el rox5 r1p r4pea r5pent rp5er. r3pet
rp4h4 rp3ing r3po r1r4 rre4c rre4f r4reo rre4st rri4o rri4v rron4 rros4 rrys4
4rs2 r1sa rsa5ti rs4c r2se r3sec rse4cr rs5er. rs3es rse5v2 r1sh r5sha r1si
r4si4b rson3 r1sp r5sw rtach4 r4tag r3teb rten4d rte5o r1ti rt5ib rti4d r4tier
r3tig rtil3i rtil4l r4tily r4tist r4tiv r3tri rtroph4 rt4sh ru3a ru3e4l ru3en
ru4gl ru3in rum3pl ru2n runk5 run4ty r5usc ruti5n rv4e rvel4i r3ven rv5er.
r5vest r3vey r3vic rvi4v r3vo r1w ry4c 5rynge ry3t sa2 2s1ab 5sack sac3ri s3act
5sai salar4 sal4m sa5lo sal4t 3sanc san4de s1ap sa5ta 5sa3tio sat3u sau4 sa5vor
5saw 4s5b scan4t5 sca4p scav5 s4ced 4scei s4ces sch2 s4cho 3s4cie 5scin4d scle5
s4cli scof4 4scopy scour5a s1cu 4s5d 4se. se4a seas4 sea5w se2c3o 3sect 4s4ed
se4d4e s5edl se2g seg3r 5sei se1le 5self 5selv 4seme se4mol sen5at 4senc sen4d
s5ened sen5g s5enin 4sentd 4sentl sep3a3 4s1er. s4erl ser4o 4servo s1e4s se5sh
ses5t 5se5um 5sev sev3en sew4i 5sex 4s3f 2s3g s2h 2sh. sh1er 5shev sh1in sh3io
3ship shiv5 sho4 sh5old shon3 shor4 short5 4shw si1b s5icc 3side. 5sides 5sidi
si5diz 4signa sil4e 4sily 2s1in s2ina 5sine. s3ing 1sio 5sion sion5a si2r sir5a
1sis 3sitio 5siu 1siv 5siz sk2 4ske s3ket sk5ine sk5ing s1l2 s3lat s2le slith5
2s1m s3ma small3 sman3 smel4 s5men 5smith smol5d4 s1n4 1so so4ce soft3 so4lab
sol3d2 so3lic 5solv 3som 3s4on. sona4 son4g s4op 5sophic s5ophiz s5ophy sor5c
sor5d 4sov so5vi 2spa 5spai spa4n spen4d 2s5peo 2sper s2phe 3spher spho5 spil4
sp5ing 4spio s4ply s4pon spor4 4spot squal4l s1r 2ss s1sa ssas3 s2s5c s3sel
s5seng s4ses. s5set s1si s4sie ssi4er ss5ily s4sl ss4li s4sn sspend4 ss2t ssur5a
ss5w 2st. s2tag s2tal stam4i 5stand s4ta4p 5stat. s4ted stern5i s5tero ste2w
stew5a s3the st2i s4ti. s5tia s1tic 5stick s4tie s3tif st3ing 5stir s1tle 5stock
stom3a 5stone s4top 3store st4r s4trad 5stratu s4tray s4trid 4stry 4st3w s2ty
1su su1al su4b3 su2g3 su5is suit3 s4ul su2m sum3i su2n su2r 4sv sw2 4swo s4y
4syc 3syl syn5o sy5rin 1ta 3ta. 2tab ta5bles 5taboliz 4taci ta5do 4taf4 tai5lo
ta2l ta5la tal5en tal3i 4talk tal4lis ta5log ta5mo tan4de tanta3 ta5per ta5pl
tar4a 4tarc 4tare ta3riz tas4e ta5sy 4tatic ta4tur taun4 tav4 2taw tax4is 2t1b
4tc t4ch tch5et 4t1d 4te. tead4i 4teat tece4 5tect 2t1ed te5di 1tee teg4 te5ger
te5gi 3tel. teli4 5tels te2ma2 tem3at 3tenan 3tenc 3tend 4tenes 1tent ten4tag
1teo te4p te5pe ter3c 5ter3d 1teri ter5ies ter3is teri5za 5ternit ter5v 4tes.
4tess t3ess. teth5e 3teu 3tex 4tey 2t1f 4t1g 2th. than4 th2e 4thea th3eas the5at
the3is 3thet th5ic. th5ica 4thil 5think 4thl th5ode 5thodic 4thoo thor5it
tho5riz 2ths 1tia ti4ab ti4ato 2ti2b 4tick t4ico t4ic1u 5tidi 3tien tif2 ti5fy
2tig 5tigu till5in 1tim 4timp tim5ul 2t1in t2ina 3tine. 3tini 1tio ti5oc tion5ee
5tiq ti3sa 3tise tis4m ti5so tis4p 5tistica ti3tl ti4u 1tiv tiv4a 1tiz ti3za
ti3zen 2tl t5la tlan4 3tle. 3tled 3tles. t5let. t5lo 4t1m tme4 2t1n2 1to to3b
to5crat 4todo 2tof to2gr to5ic to2ma tom4b to3my ton4ali to3nat 4tono 4tony
to2ra to3rie tor5iz tos2 5tour 4tout to3war 4t1p 1tra tra3b tra5ch traci4
trac4it trac4te tras4 tra5ven trav5es5 tre5f tre4m trem5i 5tria tri5ces 5tricia
4trics 2trim tri4v tro5mi tron5i 4trony tro5phe tro3sp tro3v tru5i trus4 4t1s2
t4sc tsh4 t4sw 4t3t2 t4tes t5to ttu4 1tu tu1a tu3ar tu4bi tud2 4tue 4tuf4 5tu3i
3tum tu4nis 2t3up. 3ture 5turi tur3is tur5o tu5ry 3tus 4tv tw4 4t1wa twis4 4two
1ty 4tya 2tyl type3 ty5ph 4tz tz4e 4uab uac4 ua5na uan4i uar5ant uar2d uar3i
uar3t u1at uav4 ub4e u4bel u3ber u4bero u1b4i u4b5ing u3ble. u3ca uci4b uc4it
ucle3 u3cr u3cu u4cy ud5d ud3er ud5est udev4 u1dic ud3ied ud3ies ud5is u5dit
u4don ud4si u4du u4ene uens4 uen4te uer4il 3ufa u3fl ugh3en ug5in 2ui2 uil5iz
ui4n u1ing uir4m uita4 uiv3 uiv4er. u5j 4uk u1la ula5b u5lati ulch4 5ulche
ul3der ul4e u1len ul4gi ul2i u5lia ul3ing ul5ish ul4lar ul4li4b ul4lis 4ul3m
u1l4o 4uls uls5es ul1ti ultra3 4ultu u3lu ul5ul ul5v um5ab um4bi um4bly u1mi
u4m3ing umor5o um2p unat4 u2ne un4er u1ni un4im u2nin un5ish uni3v un3s4 un4sw
unt3ab un4ter. un4tes unu4 un5y un5z u4ors u5os u1ou u1pe uper5s u5pia up3ing
u3pl up3p upport5 upt5ib uptu4 u1ra 4ura. u4rag u4ras ur4be urc4 ur1d ure5at
ur4fer ur4fr u3rif uri4fic ur1in u3rio u1rit ur3iz ur2l url5ing. ur4no uros4
ur4pe ur4pi urs5er ur5tes ur3the urti4 ur4tie u3ru 2us u5sad u5san us4ap usc2
us3ci use5a u5sia u3sic us4lin us1p us5sl us5tere us1tr u2su usur4 uta4b u3tat
4ute. 4utel 4uten uten4i 4u1t2i uti5liz u3tine ut3ing ution5a u4tis 5u5tiz u4t1l
ut5of uto5g uto5matic u5ton u4tou uts4 u3u uu4m u1v2 uxu3 uz4e 1va 5va. 2v1a4b
vac5il vac3u vag4 va4ge va5lie val5o val1u va5mo va5niz va5pi var5ied 3vat 4ve.
4ved veg3 v3el. vel3li ve4lo v4ely ven3om v5enue v4erd 5vere. v4erel v3eren
ver5enc v4eres ver3ie vermi4n 3verse ver3th v4e2s 4ves. ves4te ve4te vet3er
ve4ty vi5ali 5vian 5vide. 5vided 4v3iden 5vides 5vidi v3if vi5gn vik4 2vil
5vilit v3i3liz v1in 4vi4na v2inc vin5d 4ving vio3l v3io4r vi1ou vi4p vi5ro
vis3it vi3so vi3su 4viti vit3r 4vity 3viv 5vo. voi4 3vok vo4la v5ole 5volt 3volv
vom5i vor5ab vori4 vo4ry vo4ta 4votee 4vv4 v4y w5abl 2wac wa5ger wag5o wait5
w5al. wam4 war4t was4t wa1te wa5ver w1b wea5rie weath3 wed4n weet3 wee5v wel4l
w1er west3 w3ev whi4 wi2 wil2 will5in win4de win4g wir4 3wise with3 wiz5 w4k
wl4es wl3in w4no 1wo2 wom1 wo5ven w5p wra4 wri4 writa4 w3sh ws4l ws4pe w5s4t 4wt
wy4 x1a xac5e x4ago xam3 x4ap xas5 x3c2 x1e xe4cuto x2ed xer4i xe5ro x1h xhi2
xhil5 xhu4 x3i xi5a xi5c xi5di x4ime xi5miz x3o x4ob x3p xpan4d xpecto5 xpe3d
x1t2 x3ti x1u xu3a xx4 y5ac 3yar4 y5at y1b y1c y2ce yc5er y3ch ych4e ycom4 ycot4
y1d y5ee y1er y4erf yes4 ye4t y5gi 4y3h y1i y3la ylla5bl y3lo y5lu ymbol5 yme4
ympa3 yn3chr yn5d yn5g yn5ic 5ynx y1o4 yo5d y4o5g yom4 yo5net y4ons y4os y4ped
yper5 yp3i y3po y4poc yp2ta y5pu yra5m yr5ia y3ro yr4r ys4c y3s2e ys3ica ys3io
3ysis y4so yss4 ys1t ys3ta ysur4 y3thin yt3ic y1w za1 z5a2b zar2 4zb 2ze ze4n
ze4p z1er ze3ro zet4 2z1i z4il z4is 5zl 4zm 1zo zo4m zo5ol zte4 4z1z2 z4zy
""".split()


def liang_hyphenation_generator(seed):
    chosen = ["ceremony", "alphabetical", "bewildering", "pumper", "asteroid", "steroid",
              "terrific", "hovercraft", "programmer", "recursion", "sluggo", "milhouse"]
    for word in chosen:
        yield word, __liang_patterns
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [w.strip() for w in f if len(w) > 7]
    rng = Random(seed)
    words = rng.sample(words, 5000)
    for word in words:
        yield word, __liang_patterns


def ordinal_transform_generator(seed):
    rng, u, v = Random(seed), 1, 4
    for (i, n) in enumerate(islice(pyramid(1, 6, 6), 3000)):
        seq = [rng.randint(1, u)]
        for _ in range(n):
            seq.append(rng.choice(seq) if rng.randint(0, 99) < 70 else rng.randint(1, u))
        yield seq, i
        u += 1
        if u == v:
            u, v = 1, v + 1


def staircase_generator(seed):
    yield from [('100123',), ('301613',), ('335689',), ('502725',), ('503715',), ('602912',)]
    yield from [('10013468',), ('10167967',), ('30034569',), ('30342789',), ('50478987',)]
    rng = Random(seed)
    for n in islice(pyramid(3, 4, 3), 400):
        # A totally random digit sequence as test case
        s = random_string('0123456789', n, rng)
        yield s,
        # A digit sequence with increasing pieces for interesting edge cases
        s, curr = '', rng.randint(1, 9999)
        while len(s) < n:
            s += str(curr)
            curr = curr + rng.randint(-1, 1) if rng.randint(0, 99) < 80 else rng.randint(1, 9999)
        yield s,


def both_ways_generator(seed):
    yield from [('rererere',), ('ouch',), ('mabaabaabbabbaabbaaa',),
                ("",), ("q",), ("bigchungus",)]
    rng = Random(seed)
    m, p = 1, 0
    for n in islice(pyramid(2, 2, 4), 2000):
        alpha = lows[:(p + 2)]
        p = (p + 1) % len(lows)
        repeat = random_string(alpha, n, rng)
        left_len = rng.randint(0, 2 * n)
        left = random_string(alpha, left_len, rng)
        mid_len = rng.randint(0, 2 * n)
        mid = random_string(alpha, mid_len, rng)
        right_len = rng.randint(0, 2 * n)
        right = random_string(alpha, right_len, rng)
        text = left + repeat + mid + repeat[::-1] + right
        yield text,
    # One last check that there is no hinky Shlemiel stuff going on.
    yield 'axa' * 1000,
    yield 'z' * 10 ** 6


def best_clubs_generator(seed):
    yield [300, 250, 200, 325, 275, 350, 225, 375, 400],
    yield [7, 11],
    yield [40, 110, 210],
    yield [2, 5, 7, 10, 14],
    rng = Random(seed)
    m = 5
    for n in islice(pyramid(4, 40, 1), 150):
        holes = [rng.randint(1, m) for _ in range(n)]
        yield holes,
        m += 1


def illuminate_all_generator(seed):
    yield [0, 0, 0, 0, 0],
    yield [2, 0, 1, 0, 2],
    yield [2, 1, 3, 1, 2],
    rng = Random(seed)
    for n in islice(pyramid(3, 3, 2), 2000):
        lights = []
        grow = rng.randint(40, 100)
        while len(lights) < n:
            if len(lights) < 1 or rng.randint(1, 100) < grow:
                lights.append(rng.randint(0, 2))
            else:
                lights[-1] += 1
        yield lights,


def verify_betweenness_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 3, 2), 2000):
        perm = [i for i in range(n)]
        rng.shuffle(perm)
        m = rng.randint(1, n - 1)
        constraints = set()
        while len(constraints) < m:
            idx = sorted(rng.sample(range(n), 3))
            if rng.randint(0, 99) < 50:
                constraints.add((perm[idx[0]], perm[idx[1]], perm[idx[2]]))
            else:
                constraints.add((perm[idx[2]], perm[idx[1]], perm[idx[0]]))
        constraints = list(constraints)
        if rng.randint(0, 99) < 50:
            ci = rng.randint(0, m - 1)
            con = constraints[ci]
            if rng.randint(0, 99) < 50:
                constraints[ci] = (con[1], con[0], con[2])
            else:
                constraints[ci] = (con[0], con[2], con[1])
        yield perm, constraints


def stepping_stones_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(5, 5, 5), 50):
        m = rng.randint(2, n // 2 + 5)
        ones = set()
        x = n // 2 + rng.randint(-1, 1)
        y = n // 2 + rng.randint(-1, 1)
        while len(ones) < m:
            ones.add((x, y))
            if rng.randint(0, 1):
                x = (x + rng.randint(-3, 3)) % n
            else:
                y = (y + rng.randint(-3, 3)) % n
            ones.add((x, y))
        yield n, list(ones)


def laser_aliens_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 5, 1), 600):
        aliens = set()
        x = rng.randint(0, n - 1)
        y = rng.randint(0, n - 1)
        m = rng.randint(max(1, n // 3), 3 * n)
        while len(aliens) < m:
            aliens.add((x, y))
            if rng.randint(0, 1):
                x = rng.randint(0, n - 1)
            else:
                y = rng.randint(0, n - 1)
        yield n, sorted(aliens)


def cut_into_squares_generator(seed):
    rng = Random(seed)
    for a in range(1, 200):
        b = 1
        while b < a:
            yield a, b
            b += rng.randint(1, 30)


def collect_numbers_generator(seed):
    # Permutations up to length six should reveal logic errors.
    for k in range(1, 7):
        for p in permutations(range(k)):
            yield list(p)
    # The longer permutations with fuzz testing.
    rng = Random(seed)
    for n in islice(pyramid(7, 2, 3), 5000):
        items = list(range(n))
        rng.shuffle(items)
        yield items
    # Just to make sure that you are not being a Shlemiel.
    for n in range(10 ** 6, 0, -10 ** 5):
        perm = list(range(n))
        perm.reverse()
        for k in range(1000):
            i1 = rng.randint(0, n - 1)
            i2 = rng.randint(0, n - 1)
            perm[i1], perm[i2] = perm[i2], perm[i1]
        yield perm


def domino_tile_generator(seed):
    rng = Random(seed)
    for n in range(2, 12, 2):
        rows = [n for _ in range(n)]
        yield rows[:]
        if n > 2:
            rows[0] += 1
            rows[1] += 1
            yield rows

    for n in islice(pyramid(1, 2, 2), 70):
        prev = curr = rng.randint(5, n + 5)
        rows = []
        for _ in range(n):
            rows.append(curr)
            next_shift = rng.choice([-1, -1, 0, 0, 0, 0, 0, +1])
            if prev < curr and next_shift == -1:
                next_shift = rng.choice([0, 1])
            if prev > curr and next_shift == +1:
                next_shift = rng.choice([-1, 0])
            prev = curr
            curr += next_shift
            if curr < 2:
                curr += 1

        if sum(rows) % 2 == 1:
            rows[0] += 1
            if len(rows) > 2:
                rows[1] += 1
                rows[2] += 1
        yield rows


def wordomino_generator(seed):
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [w.strip() for w in f if len(w) == 5]  # 4 chars + newline

    # Bunch of states whose minimax search tree depth is around 12+, without
    # the alpha-beta pruning. Plenty of forced moves in the interim, fortunately.
    for word in [
        'demi', 'rapedam', 'modoras', 'cima', 'gras', 'vagen', 'heben',
        'cima', 'burichobol', 'sheras', 'basemi', 'talasak', 'plim',
        'bloc', 'alaidemi', 'ranamas', 'bleasemi', 'lastabiridemi', 'floc',
        'agra', 'tauranalen', 'fadoras', 'seasemi', 'zemi', 'burgen', 'blas',
        'ridemi', 'mrem', 'haescaryaleasemi', 'kavideasemi'
    ]:
        yield word, words


def __110(a, b, c):  # Rule 110 hardcoded
    return int((a, b, c) in ((1, 1, 0), (1, 0, 1), (0, 1, 1), (0, 1, 0), (0, 0, 1)))


def __110_forward(prev):
    n = len(prev)
    curr = [0 for _ in range(n)]
    for i in range(n):
        curr[i] = __110(prev[(i - 1) % n], prev[i], prev[(i + 1) % n])
    return curr


def reverse_110_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(4, 5, 6), 1500):
        state = __110_forward([rng.randint(0, 1) for _ in range(n)])
        yield state[:],
        for _ in range(5):
            idx = rng.randint(0, n - 1)
            state[idx] = 1 - state[idx]
            yield state[:],


def candy_share_generator(seed):
    yield from [[1], [1, 0], [0, 1], [1, 0, 1], [2, 0, 0], [0, 3, 0, 0]]
    rng = Random(seed)
    for n in islice(pyramid(4, 2, 3), 2000):
        candies = [0 for _ in range(n)]
        remain = rng.randint(3, n - 1)
        while remain > 0:
            c = min(remain, rng.randint(1, n // 10 + 1))
            candies[rng.randint(0, n - 1)] += c
            remain -= c
        yield candies


def leibniz_generator(seed):
    yield [1, -1, 1, -1, 1], [0, 1, 2, 3, 4]
    rng = Random(seed)
    n, count_until_increase, goal, heads = 5, 0, 10, [1]
    for _ in range(1500):
        if goal < 30 or rng.randint(0, 99) < 50:
            e = rng.randint(-n, n)
        else:
            den = rng.randint(2, n)
            num = rng.randint(1, den - 1)
            sign = rng.choice([-1, 1])
            e = F(sign * num, den)
        heads.append(e)
        if len(heads) > 3:
            p = rng.randint(1, min(10, len(heads) // 2))
            pos = rng.sample(range(len(heads)), p)
            yield heads, pos
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal, n, heads = 0, goal + 1, n + 1, []


def prominences_generator(seed):
    for heights in [[1], [1, 2], [2, 1], [2, 1, 2], [1, 2, 1]]:
        yield heights
    rng = Random(seed)
    for n, scale in islice(zip(pyramid(3, 3, 3), pyramid(3, 6, 10)), 5000):
        heights, change = [rng.randint(1, scale)], +1
        while len(heights) < n:
            if rng.randint(0, 99) < 40:
                change = -change
            ee = max(1, heights[-1] + change * rng.randint(1, scale))
            ee = ee if ee != heights[-1] else ee + 1
            heights.append(ee)
        while heights[-1] > scale:
            heights.append(heights[-1] - rng.randint(1, scale))
        yield heights,


def brussels_choice_step_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(1, 5, 10), 1000):
        num = random_int(rng, n, 40)
        nn = len(str(num))
        a = rng.randint(1, nn)
        b = rng.randint(1, nn)
        yield num, min(a, b), min(max(a, b), 2 + min(a, b))


def ryerson_letter_grade_generator(seed):
    yield from range(0, 150)


def is_ascending_generator(seed):
    yield [1, 2, 2]  # Because students don't read instructions
    rng = Random(seed)
    for i in range(200):
        for j in range(10):
            items = [rng.randint(-(i + 2), i + 2)]
            for k in range(i + 1):
                items.append(items[-1] + rng.randint(0, 2 * i + 1))
            yield items[:]
            if i > 2:
                for k in range(rng.randint(0, 5)):
                    idx = rng.randint(1, len(items) - 1)
                    items[idx - 1], items[idx] = items[idx], items[idx - 1]
                    yield items[:]


def safe_squares_generator(seed):
    # Start with some smol cases to aid debugging
    yield 1, []
    yield 1, [(0, 0)]
    yield 2, [(0, 1)]
    yield 2, [(0, 0), (1, 1)]
    yield 3, [(1, 1)]
    yield 3, [(0, 0), (2, 2)]
    yield 3, [(2, 0), (0, 2)]
    yield 3, [(2, 1), (1, 2)]
    yield 3, [(0, 1), (0, 2)]

    # Some cases of filling or near filling the board.
    yield 10, [(x, x) for x in range(10)]
    yield 10, [(x, 9 - x) for x in range(10)]
    yield 10, [(x, x) for x in range(0, 10, 2)]
    yield 10, [(9 - x, x) for x in range(0, 10, 2)]
    yield 10, [(x, x) for x in range(5)]
    yield 10, [(x, 9 - x) for x in range(6, 10)]

    # Okay, let's do some bigger cases also.
    yield 42, [(17, 16), (1, 40), (36, 22)]
    yield 55, [(1, 1), (1, 17), (7, 17), (1, 7)]
    yield 77, [(14, 14), (1, 4), (14, 1), (4, 14), (1, 1), (4, 4)]
    yield 100, [(99, 0), (0, 99), (0, 0), (99, 99)]

    # On to fuzzing...
    rng = Random(seed)
    for i in range(1000):
        n = rng.randint(2, 3 + i // 20)
        pn = rng.randint(0, n + 2)
        pieces = set()
        while len(pieces) < pn:
            px = rng.randint(0, n - 1)
            py = rng.randint(0, n - 1)
            if (px, py) not in pieces:
                pieces.add((px, py))
        yield n, list(pieces)


def rooks_with_friends_generator(seed):
    rng = Random(seed)
    for (n, pieces) in safe_squares_generator(seed):
        fn = rng.randint(0, len(pieces))
        yield n, pieces[:fn], pieces[fn:]
        yield n, pieces[fn:], pieces[:fn]


def first_preceded_by_smaller_generator(seed):
    rng = Random(seed)
    scale = 3
    for n in islice(pyramid(3, 3, 2), 1000):
        items = [rng.randint(0, n)]
        for _ in range(n):
            items.append(items[-1] + rng.randint(0, scale))
        rng.shuffle(items)
        yield items, rng.randint(1, n // 2)
        scale += 1


def count_and_say_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 3, 2), 2000):
        for p in [30, 50, 90]:
            yield str(random_int(rng, n, p))


def reverse_ascending_sublists_generator(seed):
    rng = Random(seed)
    s, p = 3, 50
    for n in islice(pyramid(3, 5, 3), 2000):
        d, items = rng.choice([-1, +1]), [rng.randint(-s, s)]
        for _ in range(n - 1):
            items.append(items[-1] + d * rng.randint(1, s))
            d = -d if rng.randint(0, 99) < p else d
        yield items
        s, p = s + 1, (p + 3) % 100


def give_change_generator(seed):
    rng = Random(seed)
    coins = [1]
    for _ in range(10):
        coins.append(coins[-1] + rng.randint(1, 1 + coins[-1]))
    for _ in range(1000):
        for j in range(1, 10):
            use = rng.sample(coins, j)
            use.sort(reverse=True)
            if use[-1] > 1:
                use.append(1)
            amount = 1
            while amount < 5 * use[0]:
                yield amount, use[:]
                amount += rng.randint(1, 2 + 2 * amount // 3)


def bridge_hand_generator(seed):
    rng = Random(seed)
    ranks_list = [r for r in __bridge_ranks]
    for n in range(3000):
        flip_prob = 10 + 10 * (n % 8)
        hand = set()
        suit = rng.choice(__suits)
        rank = rng.choice(ranks_list)
        while len(hand) < 13:
            hand.add((rank, suit))
            if rng.randint(0, 99) < flip_prob:
                suit = rng.choice(__suits)
            rank = rng.choice(ranks_list)
        yield list(hand),


def winning_card_generator(seed):
    rng = Random(seed)
    for _ in range(10000):
        hand = rng.sample(__bridge_deck, 4)
        for trump in __suits:
            yield hand[:], trump
        yield hand[:], None


def hand_shape_distribution_generator(seed):
    rng = Random(seed)
    for i in range(2, 50):
        hands = [rng.sample(__bridge_deck, 13) for _ in range(i * i)]
        yield hands


def milton_work_point_count_generator(seed):
    for hand in bridge_hand_generator(seed):
        hand = hand[0]
        for suit in __suits:
            yield hand, suit
        yield hand, 'notrump'


def possible_words_generator(seed):
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    rng = Random(seed)
    n = 0
    while n < 30:
        pat_word = rng.choice(words)
        letters = sorted(set(c for c in pat_word))
        if len(letters) > 3:
            g = rng.randint(3, max(4, len(letters) - 3))
            guessed = rng.sample(letters, g)
            pat = ''
            for ch in pat_word:
                pat += ch if ch in guessed else '*'
            yield words, pat
            n += 1


def postfix_evaluate_generator(seed):
    yield [42]
    rng = Random(seed)
    for n in islice(pyramid(2, 10, 10), 1000):
        exp, expr_length = [], 0
        while len(exp) < n or expr_length != 1:
            if expr_length > 1 and (expr_length > 10 or rng.randint(0, 99) < 50):
                exp.append(rng.choice(['+', '-', '*', '/']))
                expr_length -= 1
            else:
                exp.append(rng.randint(1, 10))
                expr_length += 1
        yield exp


def expand_intervals_generator(seed):
    yield ""
    rng = Random(seed)
    for n, p in islice(zip(pyramid(2, 1, 2), cycle([10, 20, 80, 100])), 1000):
        curr, result, first = 0, "", True
        for _ in range(n):
            if not first:
                result += ','
            first = False
            if rng.randint(0, 99) < p:
                result += str(curr)
                curr += rng.randint(2, 10)
            else:
                end = curr + rng.randint(1, 30)
                result += f"{curr}-{end}"
                curr = end + rng.randint(2, 10)
        yield result,


def collapse_intervals_generator(seed):
    yield from [[], [42], [1, 2], [1, 3]]
    rng = Random(seed)
    for n in islice(pyramid(3, 3, 1), 1000):
        curr = rng.randint(1, n)
        items = []
        for _ in range(n):
            items.append(curr)
            if rng.randint(0, 99) < max(5, 20 - n // 2):
                curr += rng.randint(2, n)
            else:
                curr += 1
        yield items


def __no_repeated_digits(n, allowed):
    n = str(n)
    for i in range(4):
        if n[i] not in allowed:
            return False
        for j in range(i + 1, 4):
            if n[i] == n[j]:
                return False
    return True


def bulls_and_cows_generator(seed):
    rng = Random(seed)
    for _ in range(100):
        result = []
        n = rng.randint(1, 4)
        allowed = rng.sample('123456789', 6)
        while len(result) < n:
            guess = rng.randint(1000, 9999)
            if __no_repeated_digits(guess, allowed):
                bulls = rng.randint(0, 3)
                cows = rng.randint(0, 3)
                cows = min(cows, 4 - bulls)  # ensure bulls + cows <= 4
                if not (bulls == 3 and cows == 1):  # impossible
                    result.append((guess, bulls, cows))
        yield result


def can_balance_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 4, 3), 1000):
        items, moms, s = [[], []], [0, 0], 2 * n
        for i in range(n):
            # Lucky enough to find balance, so yield it out.
            if i > 0 and moms[0] == moms[1] and items[0] != items[1]:
                yield items[0][::-1] + [rng.randint(1, s)] + items[1]
            side = 0 if moms[1] > moms[0] else 1
            other = 1 - side
            if rng.randint(0, 99) < 25:
                side, other = other, side
            m = len(items[side]) + 1
            diff = moms[other] - moms[side]
            if diff > 0 and diff % m == 0 and rng.randint(0, 99) < 30:
                v = diff // m
            else:
                v = rng.randint(1, s)
                s -= 1
            items[side].append(v)
            moms[side] += m * v
        yield items[0][::-1] + items[1]


def calkin_wilf_generator(seed):
    yield from islice(scale_random(seed, 3, 11), 70)


def fibonacci_sum_generator(seed):
    yield from range(1, 130)
    yield from islice(scale_random(seed, 100, 2), 100)


def fibonacci_word_generator(seed):
    yield from islice(scale_random(seed, 3, 6), 3400)


def josephus_generator(seed):
    rng = Random(seed)
    hop, skip = 1, 1
    for n in range(4, 50):
        for k in range(1, 2 + n // 4):
            if n > 20 > rng.randint(0, 99):
                yield hop, skip + rng.randint(2, 10) ** n
            else:
                yield hop, skip
            skip += rng.randint(1, 2 + k)
        hop += rng.randint(1, 3 + n // 20)
        skip = rng.randint(1, 5)


def balanced_ternary_generator(seed):
    yield 0  # Important edge case
    for i in range(30):
        v = 3 ** i
        yield v,
        yield v + 1,
        yield -v,
        yield -v - 1,
    for v in islice(scale_random(seed, 3, 10), 3000):
        yield v,
        yield -v,


def brangelina_generator(seed):
    n = len(__names)
    for i in range((n * (n - 1)) // 2):
        first = __names[i % n]
        second = __names[(i + i // n + 1) % n]
        yield first, second


def frequency_sort_generator(seed):
    rng = Random(seed)
    scale = 5
    for n in islice(pyramid(1, 3, 2), 2000):
        items = []
        while len(items) < n:
            if len(items) < 1 or rng.randint(0, 99) < 50:
                items.append(rng.randint(-scale, scale))
            else:
                items.append(rng.choice(items))
        if n < 30:
            scale += 1
        else:
            scale += rng.randint(1, scale // 2)
        yield items


def is_perfect_power_generator(seed):
    rng = Random(seed)
    for n in range(0, 300, 2):
        base = rng.randint(2, 3 + n // 4)
        exp = rng.randint(2, 3 + n // 10)
        off = rng.choice([0, 0, -1, +1])
        yield base ** exp - off


def sort_by_digit_count_generator(seed):
    yield [7227, 2727, 7272, 2727, 2272],
    rng = Random(seed)
    for (n, p) in zip(islice(pyramid(1, 2, 1), 1000), cycle([10, 50, 80])):
        items = []
        for _ in range(n):
            if len(items) < 2 or rng.randint(0, 99) > p:
                items.append(random_int(rng, rng.randint(1, 10 + n // 2), 70))
            else:
                m = [d for d in str(rng.choice(items))]
                rng.shuffle(m)
                if rng.randint(0, 99) < 30:
                    d = rng.choice("0123456789")
                    m[rng.randint(0, len(m) - 1)] = d
                items.append(int("".join(m)))
        yield items,


def count_divisibles_in_range_generator(seed):
    yield from [(-4, 5, 2), (4, 5, 2), (-6, 6, 3), (-1, 100, 10), (-9, 3, 3), (-10, 5, 3) ]
    rng = Random(seed)
    vals = scale_random(seed, 2, 6)
    divs = scale_random(seed, 2, 20)
    for (v, d) in islice(zip(vals, divs), 2000):
        vv = rng.randint(0, v)
        yield -vv, v, d
        yield vv, v, d
        yield -v, -vv, d
        yield -v, vv // d, d
        yield -(v // d), v, d
        yield -v, 0, d
        yield 0, v, d


def losing_trick_count_generator(seed):
    rng = Random(seed)
    for _ in range(30000):
        yield rng.sample(__bridge_deck, 13)


def riffle_generator(seed):
    rng = Random(seed)
    for i in range(1000):
        items = [rng.randint(-i * i, i * i) for _ in range(2 * i)]
        yield items[:], True
        yield items, False


def words_with_given_shape_generator(seed):
    patterns = [  # Tactically chosen patterns to give reasonably short answers
        [1, 0, 0],
        [0, 0, 1],
        [1, 0, -1, 0],
        [-1, 0, 0],
        [1, 1, 0, 1],
        [-1, 0, -1, 0, 1],
        [0, 1, 0, -1, 1],
        [1, 1, 1, 1, 1, -1, 1],
        [-1, 1, 1, 1, 1, 1, -1],
        [1, 1, -1, -1, 1, 1, 1, 1],
        [1, 1, 1, -1, 1, 1, -1, -1, -1],
        [-1, -1, -1, 1, -1, -1, 1, 1, 1],
        [1, 1, -1, 1, 1, 1, 1],
        [-1, 1, 1, 1, -1, -1, 1, -1, -1, 1, -1, 1, -1],
        [1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1],
        [-1, -1, 1, -1, 1, 1, -1, 1, 1, -1, -1],
        [-1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1],
        [1, 1, -1, 1, 1, -1, 1, -1, 1, 1, -1, 1],
        [-1, 1, 1, 1, -1, 1, 1, 1, 1],
        [1, -1, 1, 1, -1, -1, -1, 1, 1, -1, 1],
        [1, 1, -1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, -1],
        [1, 1, -1, 1, 1, -1, 1, -1, 1, 1, -1, 1],
        [-1, -1, 1, 1, -1, 1, 1, -1, -1, 1, -1, 1, 1],
        [1, 1, 1, -1, 1, 1, 1],
        [1, 1, 1, 1, 1, -1],
        [1, 1, 1, 1, -1, -1, -1],
        [-1, -1, -1, -1, 1, 1, -1]
    ]
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [line.strip() for line in f]

    for pattern in patterns:
        yield words, pattern


def squares_intersect_generator(seed):
    rng = Random(seed)
    for r in islice(pyramid(5, 10, 10), 5000):
        x1 = rng.randint(-r, r)
        y1 = rng.randint(-r, r)
        d1 = rng.randint(1, r)
        x2 = rng.randint(-r, r)
        y2 = rng.randint(-r, r)
        d2 = rng.randint(1, r)
        for k in range(1, 3):
            yield (x1, y1, k * d1), (x2, y2, k * d2)
        if r > 10:
            yield (r * x1, r * y1, r * d1), (r * x2, r * y2, r * d2)
            yield (x1, r * y1, r * d1), (x2, r * y2, r * d2)
            yield (r * x1, y1, r * d1), (r * x2, y2, r * d2)


def only_odd_digits_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(1, 5, 2), 4000):
        num = 0
        for i in range(n):
            num = 10 * num + rng.choice([1, 3, 5, 7, 9])
        yield num,
        for _ in range(2):
            p = rng.randint(0, n)
            num += (10 ** p) * rng.randint(1, 9)
            yield num,


def lattice_paths_generator(seed):
    rng = Random(seed)
    yield 2, 2, [(1, 0), (0, 1)]
    yield 5, 5, [(4, 5), (5, 4)]
    for n in islice(pyramid(2, 3, 2), 1000):
        x = n + rng.randint(0, 3)
        y = n + rng.randint(0, 3)
        tabu = set()
        m = rng.randint(n, 2 * n)
        while len(tabu) < m:
            xx, yy = x, y
            while (xx, yy) == (x, y) or (xx, yy) == (0, 0):
                xx = rng.randint(0, x)
                yy = rng.randint(0, y)
            tabu.add((xx, yy))
        yield x, y, list(tabu)


def count_carries_generator(seed):
    rng = Random(seed)
    for n, p in islice(zip(pyramid(3, 5, 1), cycle([60, 70, 80, 90, 97])), 5000):
        nums = []
        for _ in range(2):
            m = 0
            for _ in range(rng.randint(n // 2, n)):
                if rng.randint(0, 99) < p:
                    m = 10 * m + rng.randint(5, 9)
                else:
                    m = 10 * m + rng.randint(0, 4)
            nums.append(m)
        yield nums[0], nums[1]


def count_squares_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(3, 5, 3), 300):
        pts = set()
        while len(pts) < 2 * n:
            x = rng.randint(0, n)
            y = rng.randint(0, n)
            pts.add((x, y))
            if rng.randint(0, 99) < 40:
                dx = rng.randint(1, n)
                dy = rng.randint(-3, n)
                pts.add((x + dx, y + dy))
                pts.add((x + dy, y - dx))
                pts.add((x + dx + dy, y - dx + dy))
        yield sorted(pts)


def three_summers_generator(seed):
    rng = Random(seed)
    count_until_increase, goal = 0, 1
    items = []
    for i in range(200):
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal = 0, goal + 5
            items = [rng.randint(1, 2 + i)]
        items.append(items[-1] + rng.randint(1, 2 + i * i))
        if len(items) > 2:
            for _ in range(3):
                goal = sum(rng.sample(items, 3))
                goal += rng.randint(-5, 5)
                yield items[:], goal
    # To make sure that you are not being a Shlemiel.
    for i in range(5):
        items, goal = sorted(rng.sample(range(0, 2_000_000, 7), 1500)), 3_000_000
        yield items, goal


def ztalloc_generator(seed):
    yield from ((p,) for p in ['d', 'uuddd', 'ddd', 'udud', 'uduuudddd', 'uuudddddddd', 'ddudd', 'dduudd'])
    rng = Random(seed)
    for n in range(2, 10000):
        pat = []
        while n > 1:
            if n % 2 == 0:
                n = n // 2
                pat.append('d')
            else:
                n = 3 * n + 1
                pat.append('u')
        while rng.randint(0, 99) < 50:
            i = rng.randint(0, len(pat) - 1)
            pat[i] = 'u' if pat[i] == 'd' else 'd'
        yield ''.join(pat),


def sum_of_two_squares_generator(seed):
    yield from islice(scale_random(seed, 2, 5), 150)


def sum_of_distinct_cubes_generator(seed):
    yield from islice(scale_random(seed, 2, 5), 200)


def seven_zero_generator(seed):
    yield from [(7,), (70,), (7700,), (77770,), (7000000,)]
    yield from [(2860,), (1001,), (2 ** 20,), (2 ** 10 - 1,)]
    rng = Random(seed)
    m = 2
    for _ in range(200):
        yield m,
        m += rng.randint(1, 10)


def remove_after_kth_generator(seed):
    rng = Random(seed)
    count_until_increase, goal, items = 0, 5, []
    for i in range(10000):
        if len(items) > 0 and rng.randint(0, 99) < 50:
            new = rng.choice(items)
            p1 = rng.randint(0, len(items) - 1)
            p2 = rng.randint(0, len(items) - 1)
            items[p1], items[p2] = items[p2], items[p1]
        else:
            new = rng.randint(-i * i, i * i + 1)
        items.append(new)
        yield items[:], rng.randint(1, 2 + i // 100)
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal, items = 0, goal + 5, []


def __qwerty_dist():
    top = {c: (0, i) for (i, c) in enumerate("qwertyuiop")}
    mid = {c: (1, i) for (i, c) in enumerate("asdfghjkl")}
    bot = {c: (2, i) for (i, c) in enumerate("zxcvbnm")}
    keys = dict(top, **mid, **bot)
    dist = dict()
    for cc1 in lows:
        for cc2 in lows:
            (r1, c1) = keys[cc1]
            (r2, c2) = keys[cc2]
            dist[(cc1, cc2)] = (abs(r2 - r1) + abs(c2 - c1)) ** 2
    return dist


def autocorrect_word_generator(seed):
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    dist = __qwerty_dist()

    def df(c1, c2):
        return dist[(c1, c2)]

    for word in ["dysotvsdr", "entiyt", "mopp", "laval", "hellx", "sassage",
                 "bumpxious", "sapeebe", "skekeron", "ekareknyfw", "arvanat",
                 "intraducial", "tatafofomomo", "yare", "zombinos", "drezry"]:
        yield word, words, df


def pyramid_blocks_generator(seed):
    ns = scale_random(seed, 3, 10)
    ms = scale_random(seed + 1, 3, 10)
    hs = scale_random(seed + 2, 2, 15)
    yield from islice(zip(ns, ms, hs), 500)


def is_cyclops_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(1, 3, 1), 1000):
        d = rng.randint(1, n + 2)
        if d % 2 == 0 and rng.randint(0, 99) < 80:
            d += 1
        m, num = d // 2, 0
        for i in range(d):
            if i == m:
                digit = rng.choice("0000000000000000000123456789")
            else:
                digit = rng.choice("123456789" if rng.randint(0, 99) < 90 else "00123456789")
            num = 10 * num + int(digit)
        yield num,


def words_with_letters_generator(seed):
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    for letters in ["smoom", "reflux", "byoam", "xxx", "aboba", "ubsub", "rentob", "whoa"]:
        yield words, letters


def extract_increasing_generator(seed):
    rng = Random(seed)
    yield "0",
    yield "3",
    for n, p in islice(zip(pyramid(2, 3, 1), cycle([10, 20, 30, 80, 90, 100])), 3000):
        d = rng.randint(0, 9)
        digits = [d]
        for _ in range(n):
            if rng.randint(0, 99) < p:
                d = rng.randint(0, 9)
            digits.append(d)
        yield "".join(str(d) for d in digits)


def line_with_most_points_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(6, 2, 3), 500):
        points = set()
        while len(points) < n:
            x = rng.randint(-n, n)
            y = rng.randint(-n, n)
            dx = 0 if rng.randint(0, 99) < 30 else rng.randint(-n, n)
            dy = 0 if dx != 0 and rng.randint(0, 99) < 30 else rng.randint(-n, n)
            while rng.randint(0, 99) < min(95, 30 + n):
                points.add((x, y))
                x, y = x + dx, y + dy
        points = list(points)
        rng.shuffle(points)
        yield points,


def count_maximal_layers_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(1, 1, 1), 2000):
        points = set()
        while len(points) < n:
            x = rng.randint(-3 - n, 3 + n)
            y = rng.randint(-3 - n, 3 + n)
            points.add((x, y))
        points = list(points)
        yield points


def taxi_zum_zum_generator(seed):
    rng = Random(seed)
    poss, moves, goal, count_until_increase = ['L', 'R', 'F'], "", 5, 0
    for _ in range(6000):
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal, moves = 0, goal + 2, []
        moves += rng.choice(poss)
        yield moves,


def count_growlers_generator(seed):
    rng = Random(seed)
    animals, goal, count_until_increase = [], 5, 0
    for _ in range(5000):
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal, animals = 0, goal + 2, []
        animals.append(rng.choice(['cat', 'tac', 'dog', 'god']))
        yield animals[:]


def tukeys_ninthers_generator(seed):
    rng = Random(seed)
    n, items, goal, step = 0, [1], 1, 0
    for i in range(1000):
        yield items[:]
        step += 1
        if step == goal:
            step, goal = 0, goal * 3
            n += 1
            items, c = [], 0
            r = (i // 100) ** 2 + 2
            for _ in range(3 ** n):
                c += rng.randint(1, r)
                items.append(c)
        rng.shuffle(items)


def __checker_pos(n, rng):
    px = rng.randint(1, n - 2)
    py = rng.randint(1, n - 2)
    if py % 2 != px % 2:
        py += -1 if py > 0 else +1
    return px, py


def max_checkers_capture_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(8, 3, 1), 1000):
        pieces = set()
        a, b = max(2, (n * n) // 8), max(3, (n * n) // 3)
        k = rng.randint(a, b)
        px, py = __checker_pos(n, rng)
        while len(pieces) < k:
            if rng.randint(0, 99) < 50:
                px, py = __checker_pos(n, rng)
            else:
                dx, dy = rng.choice([(-2, 0), (2, 0), (0, 2), (2, 0)])
                px, py = (px + dx) % n, (py + dy) % n
            pieces.add((px, py))
        (x, y) = __checker_pos(n, rng)
        while (x, y) in pieces:
            (x, y) = __checker_pos(n, rng)
        yield n, x, y, pieces


def collatzy_distance_generator(seed):
    rng = Random(seed)
    for a in range(200):
        b = rng.randint(1, a + 5)
        yield a, b


def nearest_smaller_generator(seed):
    rng = Random(seed)
    scale = 3
    for n in islice(pyramid(1, 2, 1), 3000):
        yield [rng.randint(-scale, scale) for _ in range(n)],
        scale += 1


def domino_cycle_generator(seed):
    rng = Random(seed)
    yield [],
    yield [(4, 4)],
    yield [(1, 3)],
    yield [(2, 6), (6, 2)],
    yield [(1, 4), (5, 1)],
    yield [(3, 3), (3, 3)],
    yield [(5, 1), (1, 4)],
    for n, p in islice(zip(pyramid(3, 4, 10), cycle([0, 1, 2, 3, 5])), 5000):
        first_a = a = rng.randint(1, 6)
        b = rng.randint(1, 6)
        tiles = [(a, b)]
        for _ in range(n):
            a, b = b, rng.randint(1, 6)
            if rng.randint(0, 99) < p:
                a = rng.randint(1, 6)
            tiles.append((a, b))
        if rng.randint(0, 99) < 80:
            tiles.append((b, first_a))
        elif rng.randint(0, 99) < 50:
            tiles.append((b, rng.randint(1, 6)))
        else:
            tiles.append((rng.randint(1, 6), first_a))
        yield tiles,


def van_eck_generator(seed):
    yield from islice(scale_random(seed, 3, 4), 40)


def unscramble_generator(seed):
    rng = Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    instance_count = 0
    while instance_count < 250:
        w = rng.choice(words)
        if 2 < len(w) < 9:
            first, mid, last = w[0], list(w[1:-1]), w[-1]
            rng.shuffle(mid)
            yield words, first + "".join(mid) + last
            instance_count += 1


def crag_score_generator(seed):
    yield from [list(p) for p in product([1, 2, 3, 4, 5, 6], repeat=3)]


def midnight_generator(seed):
    rng = Random(seed)
    for _ in range(50):
        dice = []
        for _ in range(6):
            roll = []
            for _ in range(6):
                if rng.randint(1, 100) < 90:
                    roll.append(rng.choice((2, 2, 2, 3, 3, 5, 6)))
                else:
                    roll.append(rng.choice((1, 4)))
            dice.append(roll)
        yield dice,


def substitution_words_generator(seed):
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    for pattern in ["LLRR", "ABACAB", "NONONO", "WW", "HEYYEAH", "YAHHAY", "RAUMAA", "INTELLIGENCE",
                    "MELANCHALL", "MELLEMOSS", "ONOOBB", "AOOA", "INNAAN", "GOLOGG", "ECEC"]:
        yield pattern, words


def count_dominators_generator(seed):
    for f in permutations([-1, -2, -3]):
        yield list(f),
    rng = Random(seed)
    r = 4
    for n in islice(pyramid(2, 3, 4), 3000):
        items = [rng.randint(-(r * r), r * r) for _ in range(n)]
        yield items
        r += 1
    # Just to make sure that you are not being a Shlemiel.
    for n in range(10 ** 6, 0, -10 ** 5):
        perm = list(range(n))
        perm.reverse()
        for k in range(50):
            i1 = rng.randint(0, n - 1)
            i2 = rng.randint(0, n - 1)
            perm[i1], perm[i2] = perm[i2], perm[i1]
        yield perm


def optimal_crag_score_generator(seed):
    rng = Random(seed)
    for i in range(40):
        rolls = []
        while len(rolls) < 2 + (i % 5):
            dice = tuple([rng.randint(1, 6) for _ in range(3)])
            rolls.append(dice)
            if rng.randint(0, 99) < 20:
                rolls.append(rng.choice(rolls))
        yield rolls


def bulgarian_solitaire_generator(seed):
    rng = Random(seed)
    for k in range(2, 30):
        for i in range(2 + 2 * k):
            items, total = [], (k * (k + 1)) // 2
            while total > 0:
                if total > 5 and (len(items) < k + i or rng.randint(0, 99) < 40):
                    p = rng.randint(1, 5)
                else:
                    p = rng.randint(1, total)
                items.append(p)
                total -= p
            yield items, k


def manhattan_skyline_generator(seed):
    rng = Random(seed)
    scale = 1
    for (i, n) in enumerate(islice(pyramid(1, 3, 2), 3000)):
        towers = []
        w = n * n + 5
        max_area = w * w // 10
        for k in range(n):
            s = rng.randint(1, w)
            e = s + rng.randint(1, n + 1)
            max_height = 1 + max_area // (e - s)
            h = rng.randint(1, max_height)
            off = rng.randint(0, 2 + scale // 4)
            towers.append((s * scale + off, e * scale + off, h * scale))
        yield sorted(towers)
        if i % 100 == 99:
            scale *= rng.randint(2, 3)


def fractran_generator(seed):
    rng = Random(seed)
    count_until_increase, goal, prog, n = 0, 5, [], 1
    for i in range(500):
        num = rng.randint(1, 10 + i)
        den = rng.randint(1, 10 + i)
        prog.append((num, den))
        k = rng.randint(0, len(prog) - 1)
        prog[k], prog[-1] = prog[-1], prog[k]
        n = rng.randint(2, 10)
        yield n, prog[:], 10
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal, prog = 0, goal + 1, []


def scylla_or_charybdis_generator(seed):
    rng = Random(seed)
    for n in range(2, 40):
        for i in range(2, 2 * n, 2):
            pos, result, = 0, ''
            for j in range(n * i):
                if pos == n - 1:
                    move = '-'
                elif pos == -n + 1:
                    move = '+'
                elif pos == 0:
                    move = rng.choice('+-')
                elif pos < 0:
                    move = rng.choice('++-')
                else:
                    move = rng.choice('--+')
                result += move
                pos += 1 if move == '+' else -1
            # Ensure success with k == 1, if nothing else.
            result += ('+' * (n + n))
            yield result, n


def count_overlapping_disks_generator(seed):
    rng = Random(seed)
    count_until_increase, goal, max_r = 0, 5, 10
    for n in range(1, 250, 2):
        d, m = 40 * n, rng.randint(8 * n, 12 * n)
        disks = set()
        while len(disks) < m:
            x = rng.randint(-d, d)
            y = rng.randint(-d, d)
            r = rng.randint(1, max_r)
            disks.add((x, y, r))
        disks = list(disks)
        yield disks
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal = 0, goal + 2
            max_r += 5


def arithmetic_progression_generator(seed):
    rng = Random(seed)
    i = 3
    for n, p in islice(zip(pyramid(10, 2, 2), cycle([10, 20, 30, 90])), 2000):
        elements = set()
        start = rng.randint(1, i + 3)
        step = rng.randint(1, i + 2)
        while len(elements) < n:
            elements.add(start)
            start += step
            if rng.randint(0, 99) < p:
                start = rng.randint(1, i * i + 3)
                step = rng.randint(1, i + 2)
        yield sorted(elements),
        i += 1


def cookie_generator(seed):
    rng = Random(seed)
    for i in range(25):
        items = [rng.randint(1, 2 + i)]
        for j in range(3 + i // 7):
            items.append(items[-1] + rng.randint(1, 2 + i))
        yield items


def eliminate_neighbours_generator(seed):
    for n in range(1, 7):
        for p in permutations(range(1, n + 1)):
            yield list(p)
    rng = Random(seed)
    count_until_increase, goal = 0, 1
    items, m = [1, 2, 3, 4, 5, 6, 7], 7
    for i in range(2000):
        yield items[:]
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal = 0, goal + 3
            m = 8 + i // 50
            items = list(range(1, m))
        items.append(m)
        m += 1
        j = rng.randint(0, len(items) - 1)
        items[j], items[-1] = items[-1], items[j]
    for n in range(100, 1501):
        items = [i + 1 for i in range(n)]
        i1 = rng.randint(0, n // 2)
        i2 = rng.randint(0, n // 2)
        items[i1], items[i2] = items[i2], items[i1]
        yield items[:]
        yield list(reversed(items))


def counting_series_generator(seed):
    yield from islice(scale_random(seed, 5, 2), 1000)


def wythoff_array_generator(seed):
    rng = Random(seed)
    curr, step = 1, 1
    for _ in range(300):
        yield curr
        curr += rng.randint(1, 4 * step)
        step += 1


def hourglass_flips_generator(seed):
    rng = Random(seed)
    for _ in range(50):
        glasses, curr = [], rng.randint(6, 11)
        for j in range(rng.randint(2, 4)):
            low = 0 if rng.randint(0, 99) < 60 else rng.randint(5, max(6, curr // 2))
            glasses.append((curr, low))
            curr += rng.randint(1, 5)
        t = rng.randint(curr + 2, 2 * curr)
        yield glasses, t


def knight_jump_generator(seed):
    rng = Random(seed)
    for i in range(10000):
        k = 2 + i % 50
        steps = [1]
        for _ in range(1, k):
            steps.append(steps[-1] + rng.randint(1, 5))
        start = [rng.randint(10, 20) for _ in range(k)]
        rng.shuffle(steps)
        end = [x + y * rng.choice([-1, 1])
               for (x, y) in zip(start, steps)]
        if rng.randint(1, 100) < 50:
            end[rng.randint(0, k - 1)] += 1
        steps.sort(reverse=True)
        yield tuple(steps), tuple(start), tuple(end)


def frog_collision_time_generator(seed):
    rng = Random(seed)
    instance_count = 0
    while instance_count < 5000:
        c = [rng.randint(-10, 10) for _ in range(6)]
        if c[2:4] == c[4:6] or c[2:4] == [0, 0] or c[4:6] == [0, 0]:
            continue
        t = rng.randint(1, 2 + 2 ** (instance_count // 100))
        x1, y1 = c[0] + t * c[2], c[1] + t * c[3]
        x2, y2 = c[0] + t * c[4], c[1] + t * c[5]
        if rng.randint(1, 100) < 30:
            if rng.randint(1, 100) < 50:
                x1 += rng.choice([-10, 10])
            else:
                y1 += rng.choice([-10, 10])
        elif rng.randint(1, 100) < 10:
            c[2], c[3] = -c[2], -c[3]
        if (x1, x2) != (y1, y2):
            yield (x1, y1, -c[2], -c[3]), (x2, y2, -c[4], -c[5])
            instance_count += 1


def spread_the_coins_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(5, 3, 2), 500):
        coins = [0 for _ in range(n)]
        coins[-1] = 1
        m = rng.randint(2 * n, 3 * n)
        while m > 0:
            c = rng.randint(1, 4)
            i = rng.randint(0, n - 1)
            coins[i] += c
            m -= c
        u = rng.randint(2, 2 + max(coins) // 2)
        left = rng.randint(1, u - 1)
        yield coins, left, u - left


def group_and_skip_generator(seed):
    rng = Random(seed)
    for n in islice(scale_random(seed, 2, 10), 400):
        b = rng.randint(1, max(2, n // 100))
        a = rng.randint(b + 1, 2 * b + 1)
        yield n, a, b


def nearest_polygonal_number_generator(seed):
    rng = Random(seed)
    yield from [(7, 3), (7, 4), (8, 3), (10, 9), (12, 4), (15, 6), (19, 7)]
    curr = 20
    for i in range(250):
        for j in range(15):
            curr = curr + rng.randint(1, curr // 10)
            s = rng.randint(3, i + 3)
            yield curr, s
        curr = curr * 2


def subtract_square_generator(seed):
    rng = Random(seed)
    for i in range(1, 9):
        curr = rng.randint(1, 10)
        query = []
        for j in range(2 * i):
            query.append(curr)
            curr = (4 * curr) // 3 + rng.randint(1, max(3, curr // 3))
        yield query


def duplicate_digit_bonus_generator(seed):
    rng = Random(seed)
    n, count_until_increase, goal = 1, 0, 5
    for _ in range(3000):
        yield random_int(rng, n, 60)
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal, n = 0, goal + 5, n + 1


def hitting_integer_powers_generator(seed):
    rng = Random(seed)
    for n in islice(pyramid(2, 5, 10), 100):
        pn = __primes[:n]
        a = rng.choice(pn)
        b = rng.choice(pn)
        for p in __primes[:n]:
            if rng.randint(0, 99) < 20:
                a = a * p
            if rng.randint(0, 99) < 20:
                b = b * p
        yield a, b, 10 ** (rng.randint(1, min(4, n)))


def permutation_cycles_generator(seed):
    # All permutations up to length 5
    for n in range(1, 6):
        for p in permutations(range(n)):
            yield list(p)
    # Fuzz test some longer permutations
    rng = Random(seed)
    for n in islice(pyramid(6, 2, 3), 1000):
        for _ in range(n // 2):
            perm = list(range(n))
            rng.shuffle(perm)
            yield perm


def word_height_generator(seed):
    rng = Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    for _ in range(5000):
        idx = rng.randint(0, len(words) - 1)
        yield words, words[idx]


def mcculloch_generator(seed):
    rng = Random(seed)
    for _ in range(5000):
        n = []
        # Produce only digit strings whose evaluation terminates.
        for _ in range(rng.randint(0, 7)):
            n.append(rng.choice('345'))
        n.append('2')  # Need to have one of these
        for _ in range(rng.randint(1, 7)):
            n.append(rng.choice('123456789'))
        yield "".join(n)


def trips_fill_generator(seed):
    rng = Random(seed)
    with open('words_sorted.txt', encoding='UTF-8') as f:
        words3 = [word.strip() for word in f if len(word) == 4]
    for i in range(130):
        n, pat, c = 3 + i // 20, '', 0
        for _ in range(n):
            if rng.randint(0, 99) < 100 - 15 * (c + 2):
                pat += '*'
                c += 1
            else:
                pat += rng.choice(rng.choice(words3))
                c = 0
        yield words3, pat, []


def is_left_handed_generator(seed):
    for d in product([1, 6], [2, 5], [3, 4]):
        for p in permutations(list(d)):
            yield list(p),


def balanced_centrifuge_generator(seed):
    rng = Random(seed)
    for n in range(1, 500):
        k = 1
        while k <= n:
            yield n, k
            step = 1 if n < 50 else rng.randint(1, 3 + n // 10)
            k += step


def lunar_multiply_generator(seed):
    for a in islice(scale_random(seed, 2, 3), 100):
        for b in scale_random(seed + a, 2, 3):
            if b > a:
                break
            else:
                yield a, b
                yield b, a


def oware_move_generator(seed):
    rng = Random(seed)
    k, goal = 2, 10
    for i in range(5000):
        to_sow = rng.randint(0, 6 * k * k * k * k)
        sown = 0
        board = [0 for _ in range(2 * k)]
        while sown * sown < to_sow:
            pos = rng.randint(0, 2 * k - 1)
            board[pos] += 1
            sown += 1
        for house in range(k):
            if board[house] > 0:
                yield board[:], house
        tall = rng.randint(0, k - 1)
        board[tall] += 2 * k + rng.randint(2, 6 * k)
        yield board[:], tall
        if i == goal:
            goal = goal * 3
            k += 1


# Adapted from https://www.lawlessspanish.com

__ar = ['amar', 'ayudar', 'bailar', 'cambiar', 'caminar', 'cantar',
        'contestar', 'dejar', 'entrar', 'escuchar', 'esperar', 'expresar',
        'ganar', 'gastar', 'hablar', 'lavar', 'limpiar', 'llamar',
        'llegar', 'mandar', 'marchar', 'mirar', 'montar', 'nadar',
        'olvidar', 'parar', 'preparar', 'quedar', 'tirar', 'tocar',
        'tomar', 'trabajar', 'viajar']
__er = ['absorber', 'aprender', 'barrer', 'beber', 'comer', 'comprender',
        'conceder', 'correr', 'deber', 'meter', 'prender', 'poseer',
        'romper', 'sorprender', 'temer', 'toser', 'vender']
__ir = ['añadir', 'abrir', 'aplaudir', 'asistir', 'compartir', 'consumir',
        'decidir', 'definir', 'describir', 'discutir', 'dividir', 'escribir',
        'imprimir', 'insistir', 'persistir', 'prohibir', 'recibir',
        'subir', 'vivir']
__subjects = ['yo', 'tú', 'él', 'ella', 'usted', 'nosotros', 'nosotras',
              'vosotros', 'vosotras', 'ellos', 'ellas', 'ustedes']
__tenses = ['presente', 'pretérito', 'imperfecto', 'futuro']


def conjugate_regular_generator(seed):
    for verbs in zip_longest(__ar, __er, __ir):
        for verb in verbs:
            if verb:  # != None
                for subject in __subjects:
                    for tense in __tenses:
                        yield verb, subject, tense


def reach_corner_generator(seed):
    yield 1, 1, 3, 3, []
    yield 1, 1, 4, 5, [(0, 4), (3, 4), (3, 0)]
    yield 1, 0, 4, 4, []
    yield 0, 2, 5, 5, []
    yield 4, 4, 9, 9, [(0, 0), (0, 8), (8, 0), (8, 8)]
    yield 1, 1, 1000, 2, [(0, 0), (0, 1), (999, 0)]
    yield 1, 1, 1000, 2, [(0, 0), (0, 1), (999, 1)]

    rng = Random(seed)
    count_until_increase, goal, nn, aliens, n, m = 0, 1, 7, [], 0, 0
    for _ in range(5000):
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal, nn, aliens = 0, goal + 1, nn + 1, []
            n = rng.randint(4, nn - 3)
            m = rng.randint(nn - n + 2, nn)
            if n % 2 == 0 and m % 2 == 0:
                m += 1
        ex = rng.randint(0, n - 1)
        ey = rng.randint(0, m - 1)
        if (ex, ey) not in aliens:
            aliens.append((ex, ey))
        x, y = ex, ey
        while (x, y) in aliens:
            x = rng.randint(0, n - 1)
            y = rng.randint(0, m - 1)
        yield x, y, n, m, aliens[:]


def bulgarian_cycle_generator(seed):
    yield [1],
    yield [3],
    yield [2, 0, 0, 2, 6, 12, 20, 30, 42, 56],
    rng = Random(seed)
    count_until_increase, goal, n, piles = 0, 2, 5, []
    for _ in range(300):
        piles.append(rng.randint(1, n))
        piles.append(rng.randint(1, n))
        pos = rng.randint(0, len(piles) - 1)
        piles[-1] += piles[pos]
        del piles[pos]
        yield piles[:]
        count_until_increase += 1
        if count_until_increase == goal:
            count_until_increase, goal, n, piles = 0, goal + 2, n + 1, []
    for n in range(10, 30):
        yield [(i - 1) * (i - 2) for i in range(n)]


def colour_trio_generator(seed):
    rng = Random(seed)
    items = ''
    for n in islice(pyramid(3, 4, 1), 5000):
        items += rng.choice('ryb')
        yield items
        if len(items) == n:
            items = rng.choice('ryb')


def schmalz_generator(seed):
    yield "Uncle Egg White and Obi-Wan Tsukenobi are the very best of the enterprising rear.",
    yield "Spread love everywhere you go. Let no one ever come to you without leaving happier.",
    yield "When you reach the end of your rope, tie a knot in it and hang on.",
    yield "Why do you laugh? I chose death.",
    yield "All you Calabrese do the mambo like a-crazy",
    yield 'These are the people you protect with your pain!',
    yield "Aye, yeah, hey, aah! You and our auergauer is a banana foobie doobie.",
    yield "KiDs ThEsE dAyS tAlK lIkE aLl SaRcAsTiC tHiS wAy",
    yield "We had to sacrifice a couple of miners to free Bolivia.",
    yield "Always remember that you are absolutely unique. Just like everyone else.",
    yield "Don't judge each day by the harvest you reap but by the seeds that you plant.",
    yield "The future belongs to those who believe in the beauty of their dreams.",
    yield "Tell me and I forget. Teach me and I remember. Involve me and I learn.",
    yield "The best and most beautiful things in the world cannot be seen or even touched " + \
          "— they must be felt with the heart."
    yield "It is during our darkest moments that we must focus to see the light.",
    yield "Who's the leader of the club that's made for you and me? T-R-I-C-K-Y M-O-U-S-E! Tricky Mouse! " + \
          "TRICKY MOUSE! Tricky Mouse! TRICKY MOUSE! Forever let us hold our Hammers high! High! High! High!",
    yield "What puny mortal can comprehend the Mighty Mind of Galactus?",
    yield "To crush your enemies, to see them driven before you, and hear the lamentation of their women.",
    yield "Everything that irritates us about others can lead us to an understanding of ourselves.",
    yield "Trying to define yourself is like trying to bite your own teeth.",
    yield "Inability to accept the mystic experience is more than an intellectual handicap. Lack of " + \
          "awareness of the basic unity of organism and environment is a serious and dangerous hallucination."
    yield '“Evil” read backwards is “live.” Demon est deus inversus.'
    yield "想像一下清晨的多維蜘蛛網，上面佈滿了露珠",
    yield "Өндөг бол эго, шувуу бол чөлөөлөгдсөн Би юм.",
    yield "Mỗi người trong chúng ta đều là một khẩu độ mà qua đó toàn bộ vũ trụ nhìn ra.",
    yield "“Ukufuna chiyani? Nchiyani chimakupangitsa iwe kuyabwa? Kodi mukufuna mutakhala bwanji?”",
    yield "Chīwit mī xyū̀ nı ch̀wng welā nī̂ thèānận læa nı k̄hṇa nī̂ k̆ mị̀mī thī̀ s̄îns̄ud læa pĕn " + \
          "ni rạn dr̒ s̄ảh̄rạb ch̀wng welā pạccubạn nận lĕk māk k̀xn thī̀ reā ca wạd dị̂ mạn k̆ h̄āy pị " + \
          "tæ̀ k̆ yạng mī xyū̀ tlxd pị"
    yield "Do not suppose, however, that we are merely a society of lotus-eaters, lolling on divans " + \
          "and cuddling lovely women."
    yield "Agus tuiscint lochtach ar fhéiniúlacht againn, gníomhaímid ar bhealach atá mí-oiriúnach dár " + \
          "dtimpeallacht nádúrtha."
    yield "Fa tsy misy fifaliana amin'ny faharetana mandrakizay. " \
          + "Irintsika fotsiny izany satria foana ny ankehitriny."
    yield "àáâäæãåāèéêëēėęîïíīįìôöòóœøōõûüùúū"
    yield "!@#$%^&*(){}:;'[]'"
    yield "lowercaselettersonlyhere"


def count_troikas_generator(seed):
    yield from [[], [42], [42, 17], [17, 42], [-5, 0], [10 ** 42]]
    scale, rng = 4, Random(seed)
    for n, p in islice(zip(pyramid(3, 2, 1), cycle([30, 50, 70])), 6000):
        items = [rng.randint(-scale, scale)]
        for _ in range(n - 1):
            items.append(rng.choice(items) if rng.randint(0, 99) < p else rng.randint(-scale, scale))
        yield items
        scale += 1


def count_corners_generator(seed, slices=3000):
    rng = Random(seed)
    for n in islice(pyramid(3, 4, 3), slices):
        points = set()
        x = rng.randint(0, 2 + n // 5)
        y = rng.randint(0, 2 + n // 5)
        while len(points) < n:
            if rng.randint(0, 99) < 30:
                x = rng.randint(0, 2 + n // 5)
                y = rng.randint(0, 2 + n // 5)
            h = rng.randint(1, 2 + n // 2)
            if rng.randint(0, 99) < 80:
                points.add((x, y))
            points.add((x + h, y))
            points.add((x, y + h))
            if rng.randint(0, 99) < 50:
                x = x + h
            else:
                y = y + h
        yield sorted(points)


# List of test case generators for the functions recognized by this tester version.

testcases = [
    # Removed from problem set April 20, 2020
    # (
    # "connected_islands",
    # connected_islands_generator(seed),
    # "ceafc55f58a4f921582cf6fcd2c856851fca7444541e5024d1"
    # ),
    (
        "arithmetic_progression",
        arithmetic_progression_generator,
        "ace4b9a278f796dd09b2922f8b533de7747b7c0cda4f11bd067cc13133ba804b"
    ),
    (
        "count_overlapping_disks",
        count_overlapping_disks_generator,
        "a36b35b4312b28abdb6d9faa56889840bf8bcadb5c943a2dc96f066b215b84cf"
    ),
    # Removed from problem set November 26, 2021
    # (
    # "fractional_fit",
    # fractional_fit_generator,
    # "856627cc444098c9386367d5f250c0e2cddbf3ef0ecec3ba11"
    # ),
    (
        "scylla_or_charybdis",
        scylla_or_charybdis_generator,
        "b1536ef2e3dcfbd98ae4b1bb054358953a45702bb6767afc2bce3a28a229c54a"
    ),
    (
        "fractran",
        fractran_generator,
        "5ef5b21286fe7565e53230868d4240d41224a4543122ec0d5df5158b4e795dc5"
    ),
    (
        "manhattan_skyline",
        manhattan_skyline_generator,
        "cfea0db5924def2f2ecf66a69ee11a079b4d6a59f15edbd3130a2c81e2477991"
    ),
    (
        "bulgarian_solitaire",
        bulgarian_solitaire_generator,
        "819172713ddd3d5a8e596b249284a52b851b3f78d6a468b1672d10991c6d92af"
    ),
    (
        "sum_of_distinct_cubes",
        sum_of_distinct_cubes_generator,
        "d1ed5e8a0688116c7536b01804d09378a13559a0d6a9427ddf47e3dc45fbfb66"
    ),
    (
        "tukeys_ninthers",
        tukeys_ninthers_generator,
        "801d96631e1064d6bd8903f3e716bb397fa1c785877ee4e9031f0519ee5b59bb"
    ),
    (
        "optimal_crag_score",
        optimal_crag_score_generator,
        "5cf0e2ae4582c041343a113fcd4cb413c27f44ee8f4fafc6b30e60a54482ff7d"
    ),
    (
        "count_dominators",
        count_dominators_generator,
        "80709f7af6ccc56e23033b1f5b0754e262de3d1f9f70716bbb528be3e5116062"
    ),
    # Removed from problem set December 9, 2021
    # (
    #  "forbidden_substrings",
    #  forbidden_substrings_generator(seed),
    #  "6174fc0fd7c0c5b2a9bcb99a82799736ea3ab2f5f1525b8c10"
    # ),
    (
        "substitution_words",
        substitution_words_generator,
        "4cf3cd3ba0607db9ba11ec0e240391bc1e78ad62edb541d26025f8efa922cbb8"
    ),
    (
        "taxi_zum_zum",
        taxi_zum_zum_generator,
        "1612df18e6970e45150e741342232a413905b0e4cc84dd994ffde44a84b613f4"
    ),
    (
        "midnight",
        midnight_generator,
        "92890d7f13631c829d087322d0b3e6764b81063256c026ab3f9a00ae9372f963"
    ),
    (
        "crag_score",
        crag_score_generator,
        "ea62d9694e079b948a8b622c8f6dfd2aeebddeebc59c57572163678a6bdedc1e"
    ),
    (
        "unscramble",
        unscramble_generator,
        "de2b7b1ddb8bd0c74243635ed26cfebc41d2870be2ed469043de23a7eb2dd557"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "suppressed_digit_sum",
    # suppressed_digit_sum_generator(seed),
    # "69130744180a37dae42a668f28a3aa95dd53522662e058f2cf"
    # ),
    (
        "van_eck",
        van_eck_generator,
        "2938012254caba60ec8e648da870e1456d2347ea0769b8accb3c4631566f740b"
    ),
    (
        "domino_cycle",
        domino_cycle_generator,
        "63ad8f4f4cf4a1ee9f7949fb8be6c173aac5ecf19b998418fb4f8c3e9a9decda"
    ),
    # Removed from problem set August 10, 2021
    # (
    # "double_trouble",
    #  double_trouble_generator,
    # "49f103a7ad2c26d800d61e8645f967408a18c37cc6303a9dfc"
    # ),
    (
        "nearest_smaller",
        nearest_smaller_generator,
        "2406ed6b299d216019f22442d380270dff41e10fb3860276d265351b4dea08dd"
    ),
    (
        "collatzy_distance",
        collatzy_distance_generator,
        "ff638c3269c9418841d6a7f0ecf0fadb0ed02677f3b56078e09ede7ec0384f63"
    ),
    (
        "max_checkers_capture",
        max_checkers_capture_generator,
        "1547f0eb0829ff5882178f480e8c5d24f016c5c1d95038b898f17c073c3913ee"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "minimize_sum",
    # minimize_sum_generator(seed),
    # "7e6257c998d5842ec41699b8b51748400a15e539083e5a0a20"
    # ),
    (
        "count_growlers",
        count_growlers_generator,
        "3f96234a4b959581978facb1a8f44f732b5af745be4685fc963a6412a4d0932e"
    ),
    # Removed from problem set August 10, 2020
    # (
    #  "kempner",
    #  kempner_generator(seed),
    #  "dfbf6a28719818c747e2c8e888ff853c2862fa8d99683c0815"
    # ),
    (
        "words_with_letters",
        words_with_letters_generator,
        "2bb1d006c2549038711d9d61b96d551865662872f58ffb58fe97de18f3b69124"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "count_distinct_lines",
    # count_distinct_lines_generator(seed),
    # "c79db2f41e798a652e3742ef2a2b29801f0b3e52f4e285aa4e"
    # ),
    (
        "line_with_most_points",
        line_with_most_points_generator,
        "9f94d2d0edd59893f0750ddeae816051baf6c71c9d1536049ed3b2a4f3888467"
    ),
    (
        "count_maximal_layers",
        count_maximal_layers_generator,
        "950e939df6b497881a6a3dea3c2a92ac5362ff2aee2841801da38eb45867902c"
    ),
    # Removed from problem set October 29, 2021
    # (
    # "square_follows",
    # square_follows_generator,
    # "e571beecc69a7ac9235ba8911deef92b367e1badb9cff87f58"
    # ),
    (
        "extract_increasing",
        extract_increasing_generator,
        "0de18680245264367ed256c32f0563e620c700771ac5f2cf976eafe3afe4f828"
    ),
    (
        "is_cyclops",
        is_cyclops_generator,
        "48f88b82c6a22f4c51d22652f989909ffef8b98d28eb40cf57bd4a25050c853a"
    ),
    (
        "pyramid_blocks",
        pyramid_blocks_generator,
        "3bb8f8af87869b58ada39ca72e33b084524d70896619f89d91847533b89021c7"
    ),
    (
        "autocorrect_word",
        autocorrect_word_generator,
        "93742a7a15938b9184bf93cc493699b49ff8bfe07529e42d581985b23106ac47"
    ),
    (
        "remove_after_kth",
        remove_after_kth_generator,
        "3b89af0dce7e41c2fc6a851e4a35bb76f8845c5f6929ba6ade97c58d92fc3c07"
    ),
    (
        "seven_zero",
        seven_zero_generator,
        "907ec1aed8dde0ef69efc30a876af3adda28787e8c3cf67e8c0c47fa858ee9bc"
    ),
    # Removed from problem set December 10, 2020
    # (
    #  "count_distinct_sums_and_products",
    #  count_distinct_sums_and_products_generator(seed),
    #  "b75370cf5c3d2c307585937311af34e8a7ad44ea82c032786d"
    # ),
    (
        "sum_of_two_squares",
        sum_of_two_squares_generator,
        "93086670c2c63510741e58329a83fe42cc469762ca26c74130bbdf120f52e6f8"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "scrabble_value",
    # scrabble_value_generator(seed),
    # "b8b08a8a1a5fd687c49c5f7147fd35bc16d4c3ac88328ada64"
    # ),
    (
        "reverse_vowels",
        schmalz_generator,
        "db4e408209986ba0ebb9b4ebbd1b4dc170d6cafd3cfc936e9fdc218b620ae57c"
    ),
    (
        "riffle",
        riffle_generator,
        "3f5df69d458a0f72fee992fda34c18139891dcc3a63d2fe3725c600767f1da48"
    ),
    (
        "ztalloc",
        ztalloc_generator,
        "b1c4615a2b3b086a26dd8c5211f065c8227d9c138dd9bd51422c177f4ca03b14"
    ),
    (
        "losing_trick_count",
        losing_trick_count_generator,
        "c6244de2ad61ce0665114dd006b9b7d2731465d0c28780fb54fb1673d31802cf"
    ),
    (
        "postfix_evaluate",
        postfix_evaluate_generator,
        "47fb1c90b9198315bd27fb26ab2a7b3ca99d8e94e05f12c93d9594aa68089dd6"
    ),
    (
        "three_summers",
        three_summers_generator,
        "94e6dc029d76368aae6979a3abbc18be5c1aff83ff8c753b65c47ec30e3cb89c"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "is_permutation",
    # is_permutation_generator(seed),
    # "13f7265f40b407a6444d007720e680090b7b3c3a7d5c243794"
    # ),
    # Removed from problem set April 20, 2020
    # (
    # "first_missing_positive",
    # first_missing_positive_generator(seed),
    # "826ffa832d321ff26594683b3edb3123b77007f8bfc3893ac1"
    # ),
    # Removed from problem set April 20, 2020
    # (
    # "tribonacci",
    # tribonacci_generator(seed),
    # "ac64825e938d5a3104ea4662b216285f05a071cde8fd82c6fd"
    # ),
    (
        "count_squares",
        count_squares_generator,
        "cb1021c7a7e1cea05e4eb7b861df761e0d9fe94c03297f2b937726aa2f14f4d6"
    ),
    (
        "count_carries",
        count_carries_generator,
        "13888e39b86ee15b225635228719e51f229d73aa08ff57e764b69364ebd862e5"
    ),
    (
        "lattice_paths",
        lattice_paths_generator,
        "5aab78160181125a6944933dbe70acde133ae2a739798a0ce7abfb9596a28436"
    ),
    # Removed from problem set September 16, 2022
    # (
    #  "pancake_scramble",
    #  pancake_scramble_generator,
    #  "98fb3c9e30908ea6c2654d64d3c68ca2538927be529d75ddfe"
    # ),
    (
        "only_odd_digits",
        only_odd_digits_generator,
        "7775acef5b1e64bb996c997e4a0942d52cadde64987af514b2decda660f84792"
    ),
    (
        "squares_intersect",
        squares_intersect_generator,
        "fb5f90845deddea1350fa81af5a228b18a2f4922f21ce36f725d54329b89c58f"
    ),
    (
        "rooks_with_friends",
        rooks_with_friends_generator,
        "865f129cec84fdf07bad9e7fcdfa85541746c58402871ae89e2f3f62dfce4abe"
    ),
    (
        "safe_squares_rooks",
        safe_squares_generator,
        "c5c1536e0b1eebc92f5def4f1d7be4116a8a0cb48d754f2234463fc0d8a8bbf7"
    ),
    (
        "safe_squares_bishops",
        safe_squares_generator,
        "7dc0f6070c0d360dbbb8a9fa35f1c205c4dc7319f07dd1780b31280dcdce8da4"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "safe_squares_knights",
    # safe_squares_generator(seed),
    # "bcd8b6dba304f322a7789303f8d9256949fba5ef954fbe1665"
    # ),
    # Removed from problem set April 20, 2020
    # (
    # "disemvowel",
    # random_text_generator(seed),
    # "9e81bfae626ddf36655f4d3c2c36208d646eee416c18671ec1"
    # ),
    (
        "count_and_say",
        count_and_say_generator,
        "c5f25cecc498f5cba0f944bb7a8c47be7d78a5cac4797d9d282ebba489482b18"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "maximum_difference_sublist",
    # maximum_difference_sublist_generator(seed),
    # "e0e49c2c4d5ad7580fe42a71a411e8449d84c9bfd2a2b13df3"
    # ),
    (
        "first_preceded_by_smaller",
        first_preceded_by_smaller_generator,
        "7d123860240c7b8614de16f232213a81568ffd167b7cb4e8de70d6fc943dc240"
    ),
    (
        "words_with_given_shape",
        words_with_given_shape_generator,
        "9a0e08fcee10575eb6ef12de7bc5820b82b2383822beb69d2782bdace6b1894c"
    ),
    # Removed from problem set August 10, 2020
    # (
    #  "prime_factors",
    #  prime_factors_generator(seed),
    #  "fbb31e68d216d7430c47a3e3ac9eb0d4240ef2ae698eb2ded4"
    # ),
    (
        "fibonacci_sum",
        fibonacci_sum_generator,
        "e7058a191e5dbc3a8f69f302fa5f6180e8b4d4c688f6028792576010dcb3c16b"
    ),
    # Removed from the problem set August 10, 2021
    # (
    #  "factoring_factorial",
    #  factoring_factorial_generator,
    #  "be5d5249b396c259bde5338de73ae4d29831314d6c0fb9e369"
    #  ),
    (
        "bridge_hand_shorthand",
        bridge_hand_generator,
        "c6beb2fd767be441a88b1869f7cdcbae9a6b232c07165e790483bf1fe57ac699"
    ),
    (
        "milton_work_point_count",
        milton_work_point_count_generator,
        "3ff47252837a5ba8078c64e07791759067a37f940270915bf423e550635e615a"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "highest_n_scores",
    # highest_n_scores_generator(seed),
    # "978ce1599544e991c1cdc5824a762ffbed54ebcee76ca87821"
    # ),
    (
        "count_divisibles_in_range",
        count_divisibles_in_range_generator,
        "874a0000fd2c0617f73d211080c5f0a3918666aa5245d76b37d58cefd62b27d9"
    ),
    (
        "sort_by_digit_count",
        sort_by_digit_count_generator,
        "089d0fe98f13d333f85969a574dec245e433a9e30610a4d9255bb39960aa173f"
    ),
    (
        "is_perfect_power",
        is_perfect_power_generator,
        "36d9afbc5b7bb20be5f356ffb674f6bbe7be65a8e8dd697ef5cb79a8e9a7cc7d"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "iterated_remove_pairs",
    # iterated_remove_pairs_generator(seed),
    # "f3d6588ec3c251abfc024698c2a7371dcc7e175af1e41bb0aa"
    # ),
    # Removed from problem set November 30, 2020
    # (
    #  "running_median_of_three",
    #  running_median_of_three_generator(seed),
    #  "62d8c78ec1a5a7bdc9e30655380f59f59a64daacc8a272a29b"
    # ),
    (
        "frequency_sort",
        frequency_sort_generator,
        "7cf98bb630901b746d4765edaaea5d5d2ea011e1271c7214111a52c9725fe8fd"
    ),
    # Removed from problem set September 14, 2022
    # (
    #  "count_consecutive_summers",
    #  count_consecutive_summers_generator(seed),
    #  "3ade63a194b40ff5aa1b53642eee754d30f2ab48ef77330540"
    # ),
    (
        "brangelina",
        brangelina_generator,
        "f864cef7d1d71768b2efa0334e963d517290440401d98a8e85e71134a7e12c1f"
    ),
    (
        "balanced_ternary",
        balanced_ternary_generator,
        "0bfc0a405796217f5e5c11dec59016f14f031e3f2ca671597399b10c5d5120d8"
    ),
    (
        "josephus",
        josephus_generator,
        "6c39a1339f51ec7b8a29cf0a27636b6ba6be7527b75e89bac9e52ebc9ce9becf"
    ),
    # Removed from problem set December 17, 2020
    # (
    #  "aliquot_sequence",
    #  aliquot_sequence_generator(seed),
    #  "17f910bff400bb0305e94c79e27fda857c5723385d73f2ccc4"
    # ),
    # Removed from problem set April 20, 2020
    # (
    # "all_cyclic_shifts",
    # all_cyclic_shifts_generator(seed),
    # "1d06f1ef0547d8441800f2dc19aa430396a0f2e8bc414e6775"
    # ),
    (
        "fibonacci_word",
        fibonacci_word_generator,
        "95864b4e4dad5eb33d6004cb0f8092428629d4b51608f78abb1b0229525ed1e1"
    ),
    # Removed from problem set September 1, 2021
    # (
    # "create_zigzag",
    # create_zigzag_generator,
    # "6495896d5e3f0ed9c7f924b9f8c5c99a78700b1a5a1a6f8f98"
    # ),
    (
        "calkin_wilf",
        calkin_wilf_generator,
        "fd39bebe2f409e102aa1ca8de00d520ad8d3ec9f1af9a1ad0ddcc0c4721c05d5"
    ),
    (
        "can_balance",
        can_balance_generator,
        "14b7ed0b83e01874f5dd13aaad48289fe3fc9930862418b9e463c659f46f1f9a"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "contains_bingo",
    # contains_bingo_generator(seed),
    # "c352ce01918d0d47ca13adedf25556e5fd4ab1f672e07bc52f"
    # ),
    (
        "bulls_and_cows",
        bulls_and_cows_generator,
        "e00ca4cd1996a51ef5cd5588a7facd0a00f2e3f3946d5f4e96e70b65ba261ba0"
    ),
    (
        "collapse_intervals",
        collapse_intervals_generator,
        "674bb82e2076379450296d830efa0337b4a3f9068a06ea0795d79662ea4f123f"
    ),
    (
        "expand_intervals",
        expand_intervals_generator,
        "9a5a583c154073b7b308135aec7d8861bf527dff7e8b9a770e182ce166b6102d"
    ),
    (
        "reverse_ascending_sublists",
        reverse_ascending_sublists_generator,
        "099f999f059490e61c57e0845388f76f5dcbeda16be6aa422640750dcd4081a0"
    ),
    # Removed from problem set September 1, 2021
    # (
    # "reverse_reversed",
    # reverse_reversed_generator,
    # "d111344cdd8503a913181ffc7e46551b62a3dc2558a4b0fcbe"
    # ),
    # Removed from problem set December 26, 2020
    # (
    #  "longest_palindrome",
    #  longest_palindrome_generator(seed),
    #  "565387607a574740217cfeef8a301c03dad2b29f0938e98ac4"
    # ),
    # Removed from problem set April 20, 2020
    # (
    # "group_equal",
    # group_equal_generator(seed),
    # "242fac179412d7ad82bebadbd74ac7d0044b33942a714870b9"
    # ),
    (
        "ryerson_letter_grade",
        ryerson_letter_grade_generator,
        "b9b86a019c4502be825b0ed52c187f9a29106a08fbbb1ffcc67d483544a87e2f"
    ),
    (
        "is_ascending",
        is_ascending_generator,
        "a58079cfe1caa6768c9b9a2afb5f6ec3cf3e55526ab06578af3885213c3b8648"
    ),
    # Removed from problem set December 24, 2020
    # (
    #  "double_until_all_digits",
    #  double_until_all_digits_generator(seed),
    #  "7c4ba46364765cb0679f609d428bbbae8ba0df440b001c4162"
    # ),
    (
        "give_change",
        give_change_generator,
        "5c38f097ab4b39598124d3983a58a10301e012ee156ac05f1a3ad8b84c53a59e"
    ),
    (
        "winning_card",
        winning_card_generator,
        "fefd8984c1559dfde64a3ecb0d3176f26e0cb4acc6ccc6f7ea584dadb45280c0"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "hand_is_badugi",
    # hand_is_badugi_generator(987),
    # "d37917aab58ce06778d3f667f6c348d1e30ee67271d9d1de60"
    # ),
    (
        "bridge_hand_shape",
        bridge_hand_generator,
        "29e963cc7715f89d9a7f133e2a620702502f8eb5583d119dda6d58be58266102"
    ),
    (
        "hand_shape_distribution",
        hand_shape_distribution_generator,
        "b9780dbc6fbe7a317c1e3b7a88acc599a85e5baaac692cb6ccc117a272ccd06b"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "sort_by_typing_handedness",
    # sort_by_typing_handedness_generator(seed),
    # "919973a60cc556525aa38082a607f9981e83e5a58944d084af"
    # ),
    (
        "possible_words",
        possible_words_generator,
        "20d9ac2f97454ae01d482447057d4f2b2b5c001feefd781f7e02a532a694dbfb"
    ),

    # New additions to the problem set in 2020.

    (
        "cookie",
        cookie_generator,
        "e805e6415e06998231e26f5b5949ffae9f06782a5397573c8b6ff6c6358ccf61"
    ),
    (
        "eliminate_neighbours",
        eliminate_neighbours_generator,
        "24333594d079471cf6696e8b660c11fc586029a178a9879c2349d154635c6aff"
    ),
    (
        "counting_series",
        counting_series_generator,
        "cc67f4cef01c34c136a902ffea23a9df4e21b1991c491964bf89dc940067f569"
    ),
    # Removed from problem set December 9, 2021
    # (
    # "is_zigzag",
    # is_zigzag_generator,
    # "fe5e03401a32bc5ca989759708d10a7f9d2cbd9e4821566b91"
    # ),
    # Removed from problem set October 3, 2021
    # (
    # "next_zigzag",
    # next_zigzag_generator,
    # "52d66db24fc831dd08657f36e2e7b49ab788e6c86e8a25d3c5"
    # ),
    # Removed from problem set December 17, 2020
    # (
    #  "md",
    #  md_generator(seed),
    #  "a1dcac70c093c0ba7fcfeae6d9d9655accb1cf871617f2a874"
    # ),
    (
        "wythoff_array",
        wythoff_array_generator,
        "c334655a56811e0a0a3e47b2492215b13839c6fe60cfd8e9a65c784bcf3bb76d"
    ),
    (
        "hourglass_flips",
        hourglass_flips_generator,
        "d80394444051437c406c3ec73bd58d15c47d7a58c20dab5351af07607fb8ac3c"
    ),
    (
        "knight_jump",
        knight_jump_generator,
        "6a771380844685c2356a8a1eaf97376132aeb6f112bd6f68367a499579ae143a"
    ),
    (
        "frog_collision_time",
        frog_collision_time_generator,
        "2767a8f92c414656971210a1beeb83f20ad197d445897aff1076c7160574714f"
    ),
    (
        "spread_the_coins",
        spread_the_coins_generator,
        "5a1629f90f295d59d177cb99ea2b24e2c257f97b673ff77a67e286ae03b7279e"
    ),
    (
        "group_and_skip",
        group_and_skip_generator,
        "d08b0f53bff20bc4904c534a41ca6a3c7e28519dcf9185553f3ad5e88d820bba"
    ),
    (
        "nearest_polygonal_number",
        nearest_polygonal_number_generator,
        "3f4d94c36ae95bf184c292a197d42171344586d464c2e111028bda005f2286f6"
    ),
    # Removed from problem set July 8, 2020
    # (
    # "floor_power_solve",
    # floor_power_solve_generator(seed),
    # "177465906587f4bb545d546d9b9e4324a4fcbc46c2d3ec4a97"
    # ),
    (
        "subtract_square",
        subtract_square_generator,
        "4eedead71c2894be2e31e19bcf47a5a0786d70f6249a0274f2c2f14370b35990"
    ),
    # Removed from problem set December 9, 2021
    # (
    # "perimeter_limit_split",
    # perimeter_limit_split_generator,
    # "151d96f12b67f953fae52a539f669a46b734c537ed19e3ad7b"
    # ),
    (
        "duplicate_digit_bonus",
        duplicate_digit_bonus_generator,
        "7ad86f9210f78edbc645b2f9373f8f3f2cad9d2eaaa08fc0887c9e686c0b1fd5"
    ),
    # Removed from problem set September 30, 2021
    # (
    #  "count_word_dominators",
    #  count_word_dominators_generator,
    #  "ade953572b3bf2540d892ae5d6c8912cd691305a494e3d009b"
    # ),
    (
        "hitting_integer_powers",
        hitting_integer_powers_generator,
        "0d432b33fafce7477ca095a96d427fdddbc49fbe8e771d4f3d7ae87d51453559"
    ),
    (
        "permutation_cycles",
        permutation_cycles_generator,
        "995c65239a22ee31d77c32a7269f8848b694461e5b18c8d5c1f6ea37d7d19a85"
    ),
    (
        "word_height",
        word_height_generator,
        "b5454c6d98c944459ad0509a5648643feab90152f189922f36cba4763ec04e9a"
    ),
    (
        "mcculloch",
        mcculloch_generator,
        "43549317567a9c4fdd7acaa31c7684daef2c4f3b934ed63a3fe2130a0d8325b5"
    ),
    (
        "trips_fill",
        trips_fill_generator,
        "de71d54a6b5ef0aafca5fb50a6db63afb7a8744f434cc2f2a32cc2c274e8a037"
    ),
    (
        "is_left_handed",
        is_left_handed_generator,
        "5e8e432654b8352e1d293f1013c2832a029eadacb65ded537e78f0a3f48d2878"
    ),
    (
        "brussels_choice_step",
        brussels_choice_step_generator,
        "30bf08918175513337d24274aa783820c4442617e8aa78969f0dcae32ae2206a"
    ),
    (
        "balanced_centrifuge",
        balanced_centrifuge_generator,
        "2c81e311e4547c8f797955107aa6d2ae9d862c15ca61eaaad0cf364776bba8b8"
    ),
    (
        "lunar_multiply",
        lunar_multiply_generator,
        "411dfa9dc8637871c4a257df54043301308ec7c3c09ab8ac3ca2b54561256e14"
    ),
    (
        "oware_move",
        oware_move_generator,
        "7bb8b1b98cc604baf4e71970520efacca01698de168f20628dda2aa48dd8ea5e"
    ),
    (
        "conjugate_regular",
        conjugate_regular_generator,
        "132c4df527db578df034041f0cfd63eda6c98f452b9d8eb460b999558726c3ac"
    ),

    # New additions to the problem set in 2021.

    (
        "reach_corner",
        reach_corner_generator,
        "0255ef6a81a2989825f1070f5b44ab9c0ccadcb796e34bffd05b76deb5a5d07d"
    ),
    (
        "bulgarian_cycle",
        bulgarian_cycle_generator,
        "5981d20cc0a8abbbf4598a18f9a78d4916773d08044a0a7171ca8f5a9921182a"
    ),
    (
        "prominences",
        prominences_generator,
        "26b0dc947bb597270524828e885286c7e6b1ef7dba4b795ced407f9609786f62"
    ),
    (
        "leibniz",
        leibniz_generator,
        "ef3258160b68e07f3b5af2d6560d68221be321c040293d4c5493f1e6ee7e8a48"
    ),
    (
        "candy_share",
        candy_share_generator,
        "5c83954002c783e3e283cf6d9a0b8500e179f15ba6a31eb4be4db1258daa4230"
    ),
    (
        "reverse_110",
        reverse_110_generator,
        "6ea230b01e444d4000336b51a2fffa43136fb8eba59e4124f2f73c137cb4502c"
    ),
    (
        "colour_trio",
        colour_trio_generator,
        "d06b021c2742fd6e29c0617c705c3a17845a9eae5b028ad5bf2fa58718fbdbd6"
    ),
    (
        "wordomino",
        wordomino_generator,
        "5b081cc381ec8ddaa382d8450def04b53255ee62b67356f690a7eafa9efb98a5"
    ),
    (
        "count_troikas",
        count_troikas_generator,
        "9d593bfe53a18d6a6e8e355a27fa5c82efb999cf2198e60e794e3f51e16c85df"
    ),
    (
        "count_corners",
        count_corners_generator,
        "a0e7a909c954993466ab03738d160e01cd2293b8b98ceefbf8e2245ec0258454"
    ),
    (
        "cut_corners",
        count_corners_generator,
        "c467decbf7edc8c6f870ace2e158827ecc6677effd81fa4c6cd2eb34488c8f6c"
    ),
    (
        "domino_tile",
        domino_tile_generator,
        "d995b963593be92f0e3068ae9f2286159b24d03a49efb416a8c288c95c93c6c2"
    ),
    (
        "collect_numbers",
        collect_numbers_generator,
        "99afb2b51423f6223f4b51c09914f81cf6a6d12ad536e8b08bf51309c80ca798"
    ),
    (
        "cut_into_squares",
        cut_into_squares_generator,
        "fb698d6bcd2422488b6ab1acb491740e4a56f0c20e61f6ccd4f69d65f0371529"
    ),

    # New additions to the problem set in 2022.

    (
        "laser_aliens",
        laser_aliens_generator,
        "64186671716042ed9238ea75d0104cbb932a0e37e0275303f83d953a95534693"
    ),
    (
        "stepping_stones",
        stepping_stones_generator,
        "c4ac30082fa34bc0f947fc1ddf3964c92dce0acac4e7a945dec84237124d28a4"
    ),
    (
        "verify_betweenness",
        verify_betweenness_generator,
        "16b9176a15ffd0a8da7cbd5a125627fa68b6eca4ad01523515b95b0c8092f342"
    ),
    (
        "illuminate_all",
        illuminate_all_generator,
        "2b21126bfe7cc7abbfd45d6a9da7d2899a7db69bce0ffac0958d33fce3dcc7e1"
    ),
    (
        "best_clubs",
        best_clubs_generator,
        "cf82279e4ea8b4e1bd79d62c00243a210076bfb3d59dff4b0516520ff77e02f4"
    ),
    (
        "both_ways",
        both_ways_generator,
        "9bfb5ef40a0c6347cd8594aa443a10462194792cd36089acae5a00071bbeb534"
    ),
    (
        "staircase",
        staircase_generator,
        "20ceca8a5fea22f23dfba0b567555aeb5a8dc4553f03bf34b7fbb121de9d5f9e"
    ),
    (
        "ordinal_transform",
        ordinal_transform_generator,
        "de7f04aa8f6ea61b43a89bf9cce0dc594f856d7fdc7963ba12273dc09eb47568"
    ),
    (
        "liang_hyphenation",
        liang_hyphenation_generator,
        "4feb99e374834a18f50671da2b86ed65cd52143d60f59a7afe5ca2f849a01130"
    ),
    (
        "othello_moves",
        othello_moves_generator,
        "27e5957347ee99a7bd9d9925926bf6c96698c80229a2fdc7df76a42325edc47f"
    ),
    (
        "count_morse",
        count_morse_generator,
        "f3db0082e241aa3c398d6da6597ec1e0f3a65a3bba71e31929194b5a694e4400"
    ),
    (
        "count_sevens",
        count_sevens_generator,
        "c056bb61e603b5e66c1772fa72178e54e42441176b13b7ef387567313a79e81a"
    ),
    (
        "count_deadwood",
        count_deadwood_generator,
        "dd44068ef82650c1919652ddc808ad9798ece75f1196305a3a9e3a006bf47f6e"
    ),
    (
        "addition_chain",
        addition_chain_generator,
        "a2c9dfa8a7598ce1d2bd607ec8b2320b58257af7f185b6430d67e896014b30d2"
    ),

    # Additional Python problems, created starting in 2023.
    (
        "queen_captures_all",
        queen_captures_all_generator,
        "d3eecf7c5a9907d43e07bc74ad3bb8b5c754cd84298cd6c8a037d26570c1ce45"
    ),
    (
        "is_chess_960",
        is_chess_960_generator,
        "4d9b0e6c631904cf993e4736fba5c0a5bd5fd87001468f36622fb316fd1d1827"
    ),
    # Removed from problem set June 10, 2023
    # (
    #  "soundex",
    #  soundex_generator,
    #  "8569238f186e3c9fb947bfcebaa57f3d48d9a9a8727e94a4176a04f49ebc53fe"
    # ),
    (
        "sum_of_consecutive_squares",
        sum_of_consecutive_squares_generator,
        "be57860970677e4893ad158413f08c747210e0d893ebfaaf7ff2d0d22f487a6c"
    ),
    (
        "topswops",
        topswops_generator,
        "7829077541c4e84225ee30e742da1296d6c0225555736621eb5259769ebb2704"
    ),
    (
        "costas_array",
        costas_array_generator,
        "6c9c0cfc7444d56bc21418d6776512e06da634998ed3012849e1b0bba048d221"
    ),
    (
        "mian_chowla",
        mian_chowla_generator,
        "fd77ebaf2b8835e626ff9e25a1d757bca6b7186af3d6cf925113b1732e92e392"
    ),
    (
        "lindenmayer",
        lindenmayer_generator,
        "7c9f332799d297bdbff7b3a3222285356f2435edc70ccacc17dd9856bc0df830"
    ),
    (
        "word_board",
        word_board_generator,
        "875a9c2a17d746676aea8c376ea7d82cf729abb8799d3200fd6afaa7f1c02a4a"
    ),
    (
        "bowling_score",
        bowling_score_generator,
        "336d1ceb26198d467fddcdc21fa36c0995d8d5fa10985b3281d3f0b90cd768bb"
    ),
    (
        "knight_survival",
        knight_survival_generator,
        "0c1a661f8c2414a0945139d9c25aef4502927c71434a84b344724d609e41c1a8"
    ),
    (
        "accumulate_dice",
        accumulate_dice_generator,
        "0807db5f5be2ccf6dfc4c2ce8cf0e9e9a123ea2fc658a085bea1d6a563d22faa"
    ),
    (
        "largest_ones_square",
        largest_ones_square_generator,
        "b1d5012a603e85405d5148203940811110a150066243afc742aad3eab6ab5a4c"
    ),
    (
        "count_odd_sum_sublists",
        count_odd_sum_sublists_generator,
        "d3bcb659e3925df3b243b0c26889a9dc8bdc45221b0650c3c109a8461f6e9340"
    ),
    (
        "multiplicative_persistence",
        multiplicative_persistence_generator,
        "9113edadf34a5c6f66c9dae8fa101e90a64754fff952922fbb0ee70538b34415"
    ),
    (
        "bus_travel",
        bus_travel_generator,
        "ec65407429c27a358eee332724a024cdae1a71dda4706a83dc7f77df4ea6fbab"
    ),
    (
        "has_majority",
        has_majority_generator,
        "e8578d6ff24dc3a2532e247e5d95f1730871c71e26c7a0e15837a6ba5d69e8de"
    ),
    (
        "card_row_game",
        card_row_game_generator,
        "698fc8231b8cd745cb3223c986eec39f32a03426059971d6466ee9a72fe01a0c"
    ),
    (
        "smetana_interpreter",
        smetana_interpreter_generator,
        "46a70fa3ccff41c5cd08cf247513228a54113e4ca54ab18c5b4ec57a60c159cc"
    ),
    (
        "stalin_sort",
        stalin_sort_generator,
        "ee869e50c9b9def412fadb0d142a8e601d9d550921d04a1736e3a99b98a8deba"
    ),
    (
        "insertion_sort_swaps",
        stalin_sort_generator,
        "1c863b25d97baaaee165ee9a07e26b09ee6575634d5180a413836a14e6132d3b"
    ),
    (
        "optimal_blackjack",
        optimal_blackjack_generator,
        "205d163c94fb506e862b6b38b458cafb2659cb0ba2fcf9c53a507c1f1ad930e1"
    ),
    (
        "blocking_pawns",
        blocking_pawns_generator,
        "3d08794bf4533c633371fe69998e177660c6f5707241b3006d05bef2a2a524c7"
    ),
    (
        "forbidden_digit",
        forbidden_digit_generator,
        "6b39e16384361b0f4f2a6b026ac1b71c24d8ffc87317d9afd375b25a15c3af23"
    ),
    (
        "break_bad",
        break_bad_generator,
        "124006d47514ba14d9ef488020db56cefdc97fc79515b3c45e2b298ddd8eb2d1"
    ),
    (
        "keypad_words",
        keypad_words_generator,
        "3298e017820c3af9d0e3252b0b849bd7e5d96e45519ce9b748f9a324e25b5132"
    ),
    (
        "abacaba",
        abacaba_generator,
        "ea34964bd4c72b543da28e9d7044acd24423c297fdd6465314d6b5d04ea80e67"
    ),
    (
        "stern_brocot",
        stern_brocot_generator,
        "9fa761f803fdf9a7c0359611cd0a62e91445e23e3f9754d5f746e5f787576a06"
    ),
    (
        "discrete_rounding",
        discrete_rounding_generator,
        "e8683699e3667c869320bc9e772206866c64fff5a4d34374fa9686b2b4ede827"
    ),
    (
        "mu_torere_moves",
        mu_torere_moves_generator,
        "a3a4ce73fcaad2dcc182c8c94181e817d0bebb47dabe566a39383e1f5ae45b16"
    ),
    (
        "count_palindromes",
        count_palindromes_generator,
        "d169a14f48d28e5ec4ae28a03a2925d811abee9c1ef6f4472e156ff84f7e8980"
    ),
    (
        "shotgun",
        shotgun_generator,
        "0f203942549b6168cdc63cad802601252655a39e098fab2d396f52c07358cd80"
    ),
    (
        "langford_violations",
        langford_violations_generator,
        "0bfac84d1229eee67f2b0056efa5121fc7b65618b33aa28504013e4465c6d6b3"
    ),
    (
        "hofstadter_figure_figure",
        hofstadter_figure_figure_generator,
        "c2250ce763119b3bade3a84b3afb98915b7be968e4f6c25c40d7df88a21122c9"
    ),
    (
        "kimberling_expulsion",
        kimberling_expulsion_generator,
        "48771e32d9ca5633aa8185357a15ab815706e0fcb91d5ba0b4302a38530a1ba0"
    ),
    (
        "repetition_resistant",
        repetition_resistant_generator,
        "d7f292d22b9b223aabc3b3e8f9a7c512d082474f379408f69b755f380308622e"
    ),
    (
        "tog_comparison",
        tog_comparison_generator,
        "f55e23dcfc75636d3aa85e525e7b3132a1f7ae2e4c412adc01bc8be93adcada3"
    ),
    (
        "trip_plan",
        trip_plan_generator,
        "e014b488d173342b34ec6527275855dadff78b45adb6b3900f188e549d96c4ba"
    ),
    (
        "bridge_score",
        bridge_score_generator,
        "b4ba8ca19871247542d172a16c065e7f41598ada7551b54088acb928278d5476"
    ),
    (
        "squares_total_area",
        squares_total_area_generator,
        "6cf12847fd4a49b76e773364d435a433079433b18be903cc0163a13b123a7052"
    ),
    (
        "fewest_boxes",
        fewest_boxes_generator,
        "db346b93869969e0c9f496115b5ce894911c23e6f9d9a20ac3e4cc20c7875100"
    ),
    (
        "des_chiffres",
        des_chiffres_generator,
        "1f3dfbcdfbc56462ea786672124615ee2e480fb47c8a4c141c3c9b25436cab00"
    ),
    (
        "cube_tower",
        cube_tower_generator,
        "a729ad1e589e0870ae4c708b86c2c24ea496d11819e6c551ca7a35645b23e265"
    ),
    (
        "tr",
        tr_generator,
        "92039e11e76854a376b7c548520fa50277bfc023c3a5f8c9fc00b6d1886231f1"
    ),
    (
        "digit_partition",
        digit_partition_generator,
        "6b1bdd849118a4405ebc7fc3f66f7082c56be26c9fb3e39ca26278c8967dcf15"
    ),
    (
        "measure_balsam",
        measure_balsam_generator,
        "a15cdb98d1c1c6ccebc5ef47610f29d6b0cdf97ddd93baf642b148ce5718707e"
    ),
    (
        "count_distinct_substrings",
        count_distinct_substrings_generator,
        "0ea1c4446e997cf3395947bf66a01525147ab06083891da579f370d706c4b225"
    ),
    (
        "mmu_lru",
        mmu_generator,
        "1cf6e3ac363dcd3b59df1ff53cf9abdd84487747f51d32f8af4cd34f1d40e35a"
    ),
    (
        "mmu_optimal",
        mmu_generator,
        "fb6b9c3578fcd78de3953e650ea321eba4466950985b5ce56649c6a43e1eb3e1"
    ),
    (
        "vector_add_reach",
        vector_add_reach_generator,
        "a4da54deb5b13790eb6d081e4126cfa43005e2c004fdc5184d4e182e8c919a3b"
    ),
    (
        "tower_of_babel",
        tower_of_babel_generator,
        "60ed0f633b21e9ed353972241cff02fa09ff29e9425888374395959ad182281e"
    ),
    (
        "parking_lot_permutation",
        parking_lot_permutation_generator,
        "2033e14ea8323502638b89793d35bf53720a091c5eb0680eafac7e900b81b4f8"
    ),
    (
        "gijswijt",
        gijswijt_generator,
        "61727e9c59198b85f3ef3e61074a5c9b33782cd9d2ca184d70aef543f4c10877"
    ),
    (
        "markov_distance",
        markov_distance_generator,
        "68ada2f65a1bd602fbe361a9327cb59c88cc28ee0dc7671af9b0db2bb3d17ece"
    ),
    (
        "count_unicolour_rectangles",
        count_unicolour_rectangles_generator,
        "14b4467fc57c884e0a583c7659985bdd8a0c84e095ef1b581586d00f7609e126"
    ),
    (
        "max_product",
        max_product_generator,
        "639791d496fd80720d4986925a37937dfb5a8cd3025c651677796c917abca2c9"
    ),
    (
        "goodstein",
        goodstein_generator,
        "cf10c309927110702b1ad430a88e59d78b8e389f51f66b616d88770e35ba5f48"
    ),
    (
        "prize_strings",
        prize_strings_generator,
        "bf65f0be4387fca6f16e89e30257d62e5924d5173a11d44d4b62296e9e04a168"
    ),
    (
        "nice_sequence",
        nice_sequence_generator,
        "4b8d06baba51031db34501b056beded81f15c8ab83f47985c79c715fb2958aca"
    ),
    (
        "game_with_multiset",
        game_with_multiset_generator,
        "bea9a0fed502f5967a175bf0f2f0dc83269043c419f17da309c9179c435593fb"
    ),
    (
        "carryless_multiplication",
        carryless_multiplication_generator,
        "4a8271e20c0925d77b221278c0dbb23408887a52c70e2a80a5722366551db923"
    ),

    # New additions to the problem set in 2024.

    (
        "reversenacci",
        reversenacci_generator,
        "2142cca26a02e73bcf5ddd13766f394930d679081f6c9c003901003285cfd577"
    ),
    (
        "kayles",
        kayles_generator,
        "1f346bcd31387e134394072470e5c460ab8f1b342ed5ddf1a93be28e99f618b3"
    ),
    (
        "greedy_egyptian",
        greedy_egyptian_generator,
        "be7ba3e90b7c410b4eecfbcd88ecbdfc133cf22ac80dd77212927b6a0a773738"
    ),
    (
        "minimal_egyptian",
        minimal_egyptian_generator,
        "752f2bbdabaa37bb900a7642026cc257d22571ee8c09fd72949df0b9ef92c7a4"
    ),
    (
        "carving_egyptian",
        greedy_egyptian_generator,
        "a04371ff999a47545d0785566d8e3c1c813039a9029eb64c741ab9648f80006f"
    ),
    (
        "super_tiny_rng",
        super_tiny_rng_generator,
        "79462fa344225685a68470f3b8f08f017b629d46af69f1292187076b339b4d70"
    ),
    (
        "van_der_corput",
        van_der_corput_generator,
        "309c5f9f5ba1e72b5b4673f3e5e44af9376c8c5eb79d6338d8dac13e38b08ae7"
    ),
    (
        "count_cigarettes",
        count_cigarettes_generator,
        "df769dd9a0edb86107562b18451edb0bc056c6c2687170f0d2cdd139bab297a9"
    ),
    (
        "is_string_shuffle",
        is_string_shuffle_generator,
        "40bfe12ca770ab65453e07048ff1c434088fe72c80b121f1c96dbffb15cf8e3b"
    ),
    (
        "str_rts",
        str_rts_generator,
        "8c726ce515c552eaca2e31bc5dbe4ffbc5b39bc2b0a0fdafbba807e2430ac399"
    ),
    (
        "lowest_common_dominator",
        lowest_common_dominator_generator,
        "91ab36011499d313b00ccf4914c5cd9882edb4005651444ce18db035a1e39ed6"
    ),
    (
        "itky_leda",
        itky_leda_generator,
        "f7d61d769bc947f9245312a3afde7f504a2305c07d6ebd2ecd46d4d083f29fd2"
    ),
    (
        "arrow_walk",
        arrow_walk_generator,
        "0c07aa91e80a5f207853c6134686bb354c6ad3b5d86ba594a0e3926f77beb746"
    ),
    (
        "self_describe",
        self_describe_generator,
        "958fc9e2ea82deb3df48d1ab3b5002aac5e380ec85a2a09adc2f02c033202eed"
    ),
    (
        "domino_pop",
        domino_pop_generator,
        "215a96c7117b4cb58d0f08fbda0925a7d9be9b98115481dc3308c0dd9ec6420c"
    ),
    (
        "median_filter",
        median_filter_generator,
        "212a511acbcaf77584e38428867e279e6527ac0d0d89f94664456a4897a4fd32"
    ),
    (
        "longest_zigzag",
        longest_zigzag_generator,
        "cd4a2b565263afc05117d1f5eb0364de5030653a592b4177524539ed8df59bfa"
    ),
    (
        "place_disks",
        place_disks_generator,
        "a70244b21edec2d56007356b453a0ce4da992257bf9f439202ff01180c39a677"
    ),
    (
        "count_triangles",
        count_triangles_generator,
        "53d4de8947aa9973485f85bc955921be6e55df0d001facf79deb402cbe8038a3"
    ),
    (
        "pair_sums",
        pair_sums_generator,
        "6304c144f259b9f4d54cac13413a52b14e05ddd38c52056da668d33cd5836550"
    ),
    (
        "pair_swaps",
        pair_swaps_generator,
        "a500f72b1baabdcbc57e721bf7f155f1da007adeaef4ba662619b7481d0772f7"
    ),
    (
        "shapley_shubik",
        shapley_shubik_generator,
        "63fccfb0bb0a4f597c6a7ddc64964c636ef5d101568cb9c54538b96d93afabdf"
    ),
    (
        "repeating_decimal",
        repeating_decimal_generator,
        "31b2f0a173417aa2c3a290cb8711b6d5010e69d3ce22b611b59bb334df47d1c5"
    ),
    (
        "dfa",
        dfa_generator,
        "b1f19542fe54a7ef7992c5ce4834bd3293cc74635e147f381afd15c4814a6154"
    ),
    (
        "nfa",
        nfa_generator,
        "cd6773bc72eb8399618a937604d264e732e32b64399598fb7d11bb80ffb87a12"
    ),
    # Removed from problem set July 1, 2025
    #(
    #    "condorcet_election",
    #    condorcet_election_generator,
    #    "fd57f0fef51bf6082dba7e43e70781f46a063663664e1b64ff95f378ea120718"
    #),
    (
        "lychrel",
        lychrel_generator,
        "51834023cf1028fc8dbf344d6f3d9d855df27f823f0b4e7f784ca1bce6a9f2c6"
    ),
    (
        "square_lamps",
        square_lamps_generator,
        "db49769d88b3326d3d0c3ee93f8f1c894a0c8f56ec55036bab36ad70f20fab55"
    ),
    (
        "trip_flip",
        trip_flip_generator,
        "4ca25906d4c84ec6df20467e45019f5e544b6c5bbc68c6b0725b36f2b3a82d67"
    ),
    (
        "arithmetic_skip",
        arithmetic_skip_generator,
        "57ee0ab04df9acaf8dcc7930a534b8fa54333a4be71c18ea089dae3edbaf08dd"
    ),
    (
        "knight_jam",
        knight_jam_generator,
        "a2373eb6a800bb78e2f92a3087be34afd1928929d01d2905b72a94dd050691e5"
    ),
    (
        "infected_cells",
        infected_cells_generator,
        "e573d964f51ce3e60426b26785c87a5b909bb4a301410707235c7f57f951f8a8"
    ),
    (
        "twos_and_threes",
        twos_and_threes_generator,
        "c5ba8b88236187abce068fab06424c08c78eff91f535c0541780e3c534c1d10b"
    ),
    (
        "count_friday_13s",
        count_friday_13s_generator,
        "3f446c580c97403da422f017c3a2d97985e0e53bcf6cd83e74cddca18ce36d74"
    ),
    (
        "lamp_pairs",
        lamp_pairs_generator,
        "d43f2304d11ccc50301aadbcfca56fa0844a9020b7f55524c3b2d1c6b42919ef"
    ),
    (
        "lowest_fraction_between",
        lowest_fraction_between_generator,
        "2c4d4408b05463320e31e0b12c1ab7f3e3a1850a14e77810cae229a3c598e896"
    ),
    (
        "tic_tac",
        tic_tac_generator,
        "f180ff8f423758cf6539bcee68d8ed442f832b0a312946b876d13f067bd7e2ed"
    ),
    (
        "jai_alai",
        jai_alai_generator,
        "00960c8cc9d2c39525d7e99d28c49ee78ed67871afa2b0dd452cde3a19a4371f"
    ),
    (
        "unity_partition",
        unity_partition_generator,
        "352de342c6642b596e5ceeecc2eb678cfdab3121b5d2da2a00d77bd707c60d43"
    ),
    (
        "spiral_matrix",
        spiral_matrix_generator,
        "46f2fb9f90177dc1fdc4a585c4ba7976126e726ad4e5aad302413aa71bdacb7f"
    ),
    (
        "independent_dominating_set",
        independent_dominating_set_generator,
        "83bb5cb2e6fffaaecbc2fa5e0f3d5755e78849a3e1bbc668ff0e6ceae850047b"
    ),
    (
        "word_positions",
        word_positions_generator,
        "ed4ac2429d2e082f9d3091d2c5cbb0f815b730888f96f650fd35c0aab841d6d1"
    ),
    (
        "word_bin_packing",
        word_bin_packing_generator,
        "603732356a9647d992ee7171789581a7f65b3142f3c53fd974ee55b3db02d4fd"
    ),
    (
        "first_fit_bin_packing",
        first_fit_bin_packing_generator,
        "0e2f55bdbb982962c5fba2db72fd91bc29382dc9e9e0804f180f08ee9df22507"
    ),
    (
        "sneaking",
        sneaking_generator,
        "8c431e273b5b2b5ad3da921226384348038cb854228927ee992ee574227ec69a"
    ),
    (
        "is_caterpillar",
        is_caterpillar_generator,
        "2c4304fa79be635d9ba08f511d343009d7e7cb6260174e5dbfdd9f5f318df06a"
    ),
    (
        "recaman",
        recaman_generator,
        "ff9c423fa18896d442d5ac8c149ba82ca973703c380c164015d3eacd85a5e1fa"
    ),
    (
        "vertex_cover",
        vertex_cover_generator,
        "a610e498fc06f48349a441b6eb50797c89f435229f3e6b844f359f417d43b3ed"
    ),
    (
        "baker_norine_dollar_game",
        baker_norine_dollar_game_generator,
        "abea57f620a61db3755e5ed755b60aefc47ccf8d5c3ed479208d3cdfa521dc81"
    ),
    (
        "conway_coin_race",
        conway_coin_race_generator,
        "1380928afc4b166aed51bb08d836bdb5d7dd4c6923a9e36bb8e609886d069601"
    ),
    (
        "string_stretching",
        string_stretching_generator,
        "68f48dab25dccc15bbb00292d516db543e807f803ab8bf1b2b8545779be51c06"
    ),
    (
        "accumulating_merge",
        accumulating_merge_generator,
        "961d05e3ffaf939e1e7c65a7d1ab9db80b978077a5de5d1168f8766de7a838ae"
    ),
    (
        "manimix",
        manimix_generator,
        "ff4b5fe52d94d3857936edc7ba77431fd12cbfed4b67e83ec054e2f8ac220948"
    ),
    (
        "bandwidth",
        bandwidth_generator,
        "c7c8a2a383205ca058296b9638a1e5fde11cd3e9bcdbbbc95edb836863d0f863"
    ),
    (
        "set_splitting",
        set_splitting_generator,
        "1e93552d6e63b557dc9a24d6c94719201f04c022ed05fd296c223e45a7a48726"
    ),
    (
        "complex_base_decode",
        complex_base_decode_generator,
        "8794386e3201ff38ce84c29445cbd788526873b777ca186bb9dabf5cdc25c51d"
    ),
    (
        "powertrain",
        powertrain_generator,
        "27e0ae0230ba1a31b0a1d87b086fd7de7265acd7f5930721d477bdebea9fc377"
    ),
    (
        "cubes_on_trailer",
        cubes_on_trailer_generator,
        "59c38b61301115bf64ef27207b1cd7bcf88bb38844e5f250471a54942f49342b"
    ),
    (
        "tom_and_jerry",
        tom_and_jerry_generator,
        "40248c1b4f5694ef7e271507036e1f77519a5277ace9ab0dafd9dc242e70d211"
    ),
    (
        "pinch_moves",
        pinch_moves_generator,
        "cb5932ed866518ab208c571cb411e7d467dc5806995e9dfa6578b92c3b340f5f"
    ),
    (
        "power_prefix",
        power_prefix_generator,
        "161230a8ee881be370b9f7988714e68c31bdef13ceff99df0b7c088e4486b6fd"
    ),
    (
        "magic_knight",
        magic_knight_generator,
        "ab6c0a822b4f9d1b7033689a1a8db130325bd71bdbf6ce22c874a24a80bea01b"
    ),
    (
        "multiply_and_sort",
        multiply_and_sort_generator,
        "a0c2e2ff9df8551f7dc7e2fd25eeabb3ca16fae14fd7fdc4e69efd23c90d35e0"
    ),
    (
       "split_at_none",
       split_at_none_generator,
       "9ec01a9207657d477c99d6ce9f0cbb99869ebec7aea412997e2a4799baec9b2c"
    ),
    (
        "ants_on_the_rod",
        ants_on_the_rod_generator,
        "d199601b862de42ef06e267e90be194934eab6bc87822dd77a33baff895cc185"
    ),
    (
        "maximum_palindrome",
        maximum_palindrome_generator,
        "aa8ccbaa4abd872b45329771887c1ce359adfde6b5647b340209fcf6795445ac"
    ),
    (
        "gauss_circle",
        gauss_circle_generator,
        "8a35212161bea3c9ff78b70ac96169f0e0d75bcaecfb3466f7658efa08724bde"
    ),
    (
        "tchuka_ruma",
        tchuka_ruma_generator,
        "5b82c7b2cba915081985eadccfda4986c163cf7f7d72cdbc65f38d77cf7aad8c"
    ),
    (
        "factoradic_base",
        factoradic_base_generator,
        "8e4750ee12d888b3e66bd4c9410690771ca8000d3f418ec09d9cf6104ec5bf36"
    ),
    (
        "friendship_paradox",
        friendship_paradox_generator,
        "7f9ea5f8dfeddc64aebdb692aab586372ea6471e5505c84bfa44917c17de42e0"
    ),
    (
        "square_root_sum",
        square_root_sum_generator,
        "f1e732e1c1e8e4d901b30c928851acdcbe3a007f3128f76344f74e3b8ac4edb3"
    ),
    (
        "loopless_walk",
        loopless_walk_generator,
        "0fd99c7f0ab5cb5e4697293486c2f6ffe383911697a47394517e625aaa4a76e9"
    ),
    (
        "lehmer_encode",
        lehmer_encode_generator,
        "0ef0464a45f433b84b78676f92c4610e031cc66983a4be1478cf746cb7e1335f"
    ),
    (
        "lehmer_decode",
        lehmer_decode_generator,
        "b9eee47331d8cf5d85220e8e8ee947b16f820957f2e5f04ac098547e61d30605"
    ),
    (
        "cousin_explainer",
        cousin_explainer_generator,
        "0566d180608174707ffa9b420f6c650975db37c14037750c2e6c24e069ef32f9"
    ),
    (
        "odds_and_evens",
        odds_and_evens_generator,
        "4958fb6e6b2fe0bbf05cfb9ab961cea747507d6d4066d30e2c29fc00f83ec478"
    ),
    (
        "s_eval",
        s_eval_generator,
        "7bec0a24887c90dc11104cad0630718909a2bea88bb64646e67bf5eb03eddd16"
    ),
    (
        "limited_swaps",
        limited_swaps_generator,
        "d6c8b213871e4bb7e9127f696982cc464b4ec9bcc8f8763df8dd4b2b9968b5db"
    ),
    (
        "bayes_dice_update",
        bayes_dice_update_generator,
        "f59c447735f6ed20a16d0cf0691df050cf6ff3b26941b1e1f4e019b99b3c28c8"
    ),
    (
        "haircut",
        haircut_generator,
        "6b9c2be415afe750a1143d5654ff2d132342b0dd43b20d39a88ba2960880a100"
    ),
    (
        "optimal_ab_filling",
        optimal_ab_filling_generator,
        "634e9fd2c1e9d3f309baead12c00fae23b1307191eb17980eff2ab9286670bc6"
    ),
    (
        "find_all_words",
        find_all_words_generator,
        "08f8760535f584c3d238dcb2c9c465a41f7be7db6e8e524a3ca1e041d4fe4916"
    ),
    (
        "pick_it",
        pick_it_generator,
        "79f1ba044e4b254fb1382040fedde1dfff8ddbf0dafbd7e4ad99c38af35f7edd"
    ),
    (
        "front_back_sort",
        front_back_sort_generator,
        "171886df33fbc4f12bf02f0b28c75cec03422d096a3315a81c10e346ed0fa458"
    ),
    (
        "fourth_seat_opening",
        bridge_hand_generator,
        "b1ffb46b778d907a1741fc921aa411ec8acb4f0af64b392127f543032b6c5c2e"
    ),
    (
        "average_run_length",
        average_run_length_generator,
        "195e165ffa14c82d3e7db21e32fbb33f8d270b0e1c46b38f05303c52a63ad696"
    ),
    (
        "zeckendorf_decode",
        zeckendorf_decode_generator,
        "252f65ba09483657d9d28c1ff13f1714e6e97dea0a8b8d02f971185712f42861"
    ),
    (
        "post_correspondence_problem",
        post_correspondence_problem_generator,
        "1865ae70a1ecaa696d66db87afa1d4495c0f0796a6190baa3dedc22676312af5"
    ),
    (
        "is_semiconnected",
        is_semiconnected_generator,
        "45133ffcbe3f48cdbe9c49123790b4d04983b24958a652ecb7cdf1ac469ddfb8"
    ),
    (
        "poker_test",
        poker_test_generator,
        "06cb768a3d39522c91ee20fd05ab897f04d2a6933c3ecf58414ad8d628c96866"
    ),
    (
        "pebblery",
        pebblery_generator,
        "d10a947e011474f764213f5c8d037ab88798e07875747a331463b7d1b7249905"
    ),
    (
        "multiple_winner_election",
        multiple_winner_election_generator,
        "5022bb941dd85ec1a5614ee29d9ff5e3f26bf1135cabbeaa05ff0592c2ecd2d8"
    ),
    (
        "diamond_sequence",
        diamond_sequence_generator,
        "6a32ad8799cdbbca9216e786ae51dcbf248981ae5c0b09363119ae58fd176193"
    ),
    (
        "slater_velez",
        slater_velez_generator,
        "8fea69528644e8bf37155d36c5a020212923ec3f50c1699b32dc5f5a408c8f1f"
    ),
    (
        "count_increasing_paths",
        count_increasing_paths_generator,
        "acda6ba0d7ec043ee899565d82c5b48155297cfbb0450b7bbef19068d86482c5"
    ),
    (
        "count_slices_with_sum",
        count_slices_with_sum_generator,
        "45626a82c31325959799e3d09fd0397fa792947f2cb5b117c04c00b38956dc77"
    ),
    (
        "maximum_repeated_suffix",
        maximum_repeated_suffix_generator,
        "f6833c6dd732623ebc379a88298073bef65a7235885255500688397bc47381f1"
    ),
    (
        "bays_durham_shuffle",
        bays_durham_shuffle_generator,
        "b9bc3bef28f9bc768cbac97e244ac59a44cb3334f3abbff426b46aa0a938bdb1"
    ),
    (
        "chunk_sorting",
        chunk_sorting_generator,
        "17e92e31ccde20410a83a361e0c59e3ce0f25df47af3901825c656e2210185d3"
    ),
    (
        "maximal_cliques",
        maximal_cliques_generator,
        "8c459e96a4cfb536c218badf1d9880821de2640e0dc22ac0bbca299ed8c92862"
    ),
    (
        "colonel_blotto",
        colonel_blotto_generator,
        "4b9508f3f465c998c11c623d6675d72e30344fa4b173b5abd708c22dd688d7d5"
    ),
    (
        "assign_sides",
        assign_sides_generator,
        "114cfee371799bb8635842e80509fbf4c446bea627f3ef0dc599cb5349e5ffe0"
    ),
    (
        "palindrome_split",
        palindrome_split_generator,
        "28375a1f9c984bc5bdcd6bbdbcc749a967967f0545b3b15db03597779fa3e54c"
    ),
    (
        "double_ended_pop",
        double_ended_pop_generator,
        "00175df4eb6b8139a37ff3d74ee62161182dbfa916205f92f96d4ced919f3e73"
    ),
    (
        "sturm_word",
        sturm_word_generator,
        "6bbe7f566c210528b93a5a3765a14e820a81a8aad5b78866062187c95b28133f"
    ),
    (
        "partition_point",
        partition_point_generator,
        "56bd3ee3e6238ef629754b563e87b62057dac379e40a55853dcd0b48a6c3b900"
    ),
    (
        "sultans_daughter",
        sultans_daughter_generator,
        "fe1820731cefa94df3d9e5c0e7e716e454d8819c8118b67758e2c031babe249b"
    ),
    (
        "generalized_fibonacci",
        generalized_fibonacci_generator,
        "f7173e3b23a6de63aeae96c27edc69a7cd07fe933914afb8f8970ba8bc7a13ca"
    ),
    (
        "maximum_word_select",
        maximum_word_select_generator,
        "b2a166ce18ca7c2dbefb0424a549f16b3b719672eae3fab1a0e73643e98796b0"
    ),
    (
        "merge_biggest",
        merge_biggest_generator,
        "97123657509c501e0beee1dc2b94b805c73029c2ed8a3681ec1207127f043da7"
    ),
    (
        "fox_and_hounds",
        fox_and_hounds_generator,
        "b86ab1b355d10c3d9e2f5c5875fc71ea9ebfe26f7ea8316d94daf6c2e0d1160e"
    ),
    (
        "instant_runoff",
        instant_runoff_generator,
        "66383b4cbe850823a241d033ec6e85d359de89a0689a9676b9dc70397db742d2"
    ),
    (
        "to_simple_continued_fraction",
        to_simple_continued_fraction_generator,
        "c7057312966ee06ce8188f2b4f6cf9bad70ed63e0ee4fe7b851fb9631826443d"
    ),
    (
        "from_simple_continued_fraction",
        from_simple_continued_fraction_generator,
        "4a1a996e20aafa363c052afc10481266a00efa890474e963c8c6a4e60817d9e0"
    ),
    (
        "copeland_method",
        instant_runoff_generator,
        "5c33d87934bc629371033f1912b4703bf9b23c84a471c4389f1c02f88cb2851f"
    ),
    (
        "shell_sort",
        shell_sort_generator,
        "946145609c66699d5a3c30be7aff89514462232b226735e707e69bea3eefee94"
    ),
    (
        "min_max_triangle",
        min_max_triangle_generator,
        "729e6378f96b938ed940754ed2b66f2c8a36415fbadb8a9182723c6eed6dcbbd"
    ),
    (
        "maximal_repeats",
        maximal_repeats_generator,
        "fd68988c1f4f3aa72d4220e21578c4e52b606b8854cc49f9ed6025fa1370256a"
    ),
    (
        "burrows_wheeler_encode",
        burrows_wheeler_encode_generator,
        "ecdcc8c3205f851b70be6137ae368fc396d73e9cd641bbfa7d53e99a1303e1d4"
    ),
    (
        "toads_and_frogs",
        toads_and_frogs_generator,
        "7391cf0e1b70ca695766703c035f3bcc5efd620821fb41301395ee94a3387183"
    ),
    (
        "tarjans_scc",
        tarjans_scc_generator,
        "4eaa45a190930b77e93ef2f8d9ff24ab07bf1fd40b5f1489fe33cc8ffd3f18a6"
    ),
    (
        "first_singleton",
        first_singleton_generator,
        "a86fd74e08933b0f770e81692032a41c935ed22c13f7f7d98a2f8f99bdfdb91e"
    ),
    (
        "expand_string",
        expand_string_generator,
        "fb8b15963d0e6cd5b213fc7ecadd645e793be2c31cdf67adfd1a70059f59aae4"
    ),
    (
        "optimal_bridges",
        optimal_bridges_generator,
        "372de41579698654edd29b16c3b230d212e9f6001b10b54e5a87d8d1ede93ac0"
    ),
    (
        "max_three_disjoint_sublists",
        max_three_disjoint_sublists_generator,
        "8572f80f9fc27506cc33f5d8c9e2703314edaa5031b36a58c57c171ea735b155"
    ),
    (
        "sublist_sum_k",
        sublist_sum_k_generator,
        "6f13e3f0e1529d138e6b1311094955b0fb8044fc48f1088ee94f74c07a749f09"
    ),
    (
        "rational_roots",
        rational_roots_generator,
        "9effd6af83d0976902c94ac67d56d6859853e097366946ae7906469967a8e0ce"
    ),
    (
        "cyk_parser",
        cyk_parser_generator,
        "8093a88e46aedb02e8963073978fea1b4565fa7949e09e6b3807c0380bc9278b"
    ),
    (
        "approval_voting",
        approval_voting_generator,
        "fa107f28ec9e073aeb56f9a4b7120c58c224464542d761ac5e0dfe51b5aad98f"
    ),
    (
        "maximal_confusion",
        maximal_confusion_generator,
        "fa18d4d86fb5610431bbfa4090baf7c2148a48e15d5cf38009df905a4b146c3d"
    ),
    (
        "descending_suffix_game",
        descending_suffix_game_generator,
        "d6131f1f8889ef1ff5caf5b068c890b80ece265b0bc30f1f0dbb808c0eebba66"
    ),
    (
        "albuquerque_stretch",
        albuquerque_stretch_generator,
        "f4a47a2d775592f9db88edd1245ba84f2323366f28f74e2b4a8c344469ada6fb"
    ),
    (
        "knaves_of_round_table",
        knaves_of_round_table_generator,
        "4c90be9f31dfad32c7da09010e4dfd0b543cc33ff7777c7ec01537ef1d8905b9"
    ),
    (
        "falling_squares",
        falling_squares_generator,
        "2dd379e49f035d7095be6d80fa7caef2d5a57e508ea0524405ebaa8cf33b4eaf"
    ),
    (
        "queue_jockeys",
        queue_jockeys_generator,
        "e43c1c0213fde0dc5fdf4676ee371dcd0e27ba0680d48845f34ce6029b19d764"
    ),
    (
        "farthest_points",
        farthest_points_generator,
        "5ba7e29eed7e7b53ef55b7f653482471528445eadd4cf7b40507bbab589a17e8"
    ),
    (
        "vigenere",
        vigenere_generator,
        "819976cc7d87485f851b9e0757aac254455ffe6bf403703cb10075a6b25d456d"
    ),
    (
        "maximum_interval_clique",
        maximum_interval_clique_generator,
        "80d027fa2df64b69acfe52b6ba59522d0eaa2204398e44a11a685a67a007d763"
    ),
    (
        "gladiators",
        gladiators_generator,
        "3aac72f991a60868851bc73438b37b443a4b38f690f053f73bea95d00bcff919"
    ),
    (
        "maximum_overlap_intervals",
        maximum_overlap_intervals_generator,
        "2ac1d71e32c74a4fddf832b8d9947fc9aaede2032e7080e270d832bc456e6b66"
    ),
    (
        "bug_in_a_line",
        bug_in_a_line_generator,
        "203f79eb2534118989f8d7fc7f322fdb5adb9deede35c48c626b434cab2e359e"
    ),
    (
        "one_zero",
        one_zero_generator,
        "7259484c1becc0e065d55e9cdb30e21ea9fb35103277c6a195b16f62db786688"
    ),
    (
        "conway_subprime",
        conway_subprime_generator,
        "e1b3f4aa1c7063d4a625a43cf3aecb6db726fc375a902fe462f5c5643bbb725e"
    ),
    (
        "knight_watch",
        knight_watch_generator,
        "b9a051157f25825246d81ce5a72562054299d122c51a5917966a2c1f0a7b6410"
    ),
    (
        "is_prime",
        is_prime_generator,
        "6485b6675ba161ce25d4ecd643a412f55a086bad7fc9786b34a672b14be71fd7"
    ),
    (
        "goldbach",
        goldbach_generator,
        "04201fc7d17eec10d7ac1f2e3035a4efa88b56dcb272c308b43f07064261cbc7"
    ),
    (
        "car_match",
        car_match_generator,
        "4edb912344062a353a842ce17069a8c375344de5f9cd22fcf9ac4056829ef97c"
    ),
    (
        "candy_split",
        candy_split_generator,
        "aeead0c98eb576c30843f79fe494889a71bb38f2eaadb1c990177b9e1c613aa8"
    ),
    (
        "random_walk",
        random_walk_generator,
        "0354d39616a79a2e45a6023dda07e0fcae2590b4a539ebcaa3768c9298e27e42"
    ),
    (
        "strahler",
        strahler_generator,
        "a144edf60d0832a4ce441e27fa9ce9c02c682beac11f12f9b1c8a0f79c8830c9"
    ),
    (
        "spiral_walk",
        spiral_walk_generator,
        "f31f7ec0c885afe72261a9bd24ac0e73b548673221835af14ddbf5eee7dfb678"
    ),
    (
        "largest_rectangle",
        largest_rectangle_generator,
        "5e16cb4ecfe007531225efb1dfdaf3e99036cd0912f76153a944f6ef60006359"
    ),
    (
        "mixed_sort",
        mixed_sort_generator,
        "a3945fea7ec047c54bee63883e5ff3f68e75dc93bd70e70b0a555e8de096651a"
    ),
    (
        "liquid_sort",
        liquid_sort_generator,
        "1fb89b433f8900e81e946cb974be6435a46822d0f4952cdcd02c9b5f45cdb577"
    ),
    (
        "lcsis",
        lcsis_generator,
        "27d19c7e888798d919a18fc6a8dcd388439aa5b9b00afa9cca0ac2823a7d58b9"
    ),
    (
        "max_blocks",
        max_blocks_generator,
        "91cc131e28b7a563c1e7c384f78ce57d7e2243fce2d16fbd3cd1e05c526eea3a"
    ),
    (
        "equal_sum_partition",
        equal_sum_partition_generator,
        "9c9eed4fdaf446fdb0443ed4e04f820c29ae7bff426daceb1dc3e51550600628"
    ),
    (
        "tanton_necklace",
        tanton_necklace_generator,
        "b6ba76fcdb3c74134ea562eb6d606a2fcbd365ea97954670374b8570a043c171"
    ),
    (
        "yellowstone_sequence",
        yellowstone_sequence_generator,
        "510cf93f380cd4949949201e52b1b93760b3f4d0cf453be0a42692c9c11eddb7"
    ),
    (
        "levine_sequence",
        levine_sequence_generator,
        "b39311d562a3c17cca28215f0e2de3fb20fefa428840a39e3bc76e9acf5c3c22"
    ),
    (
        "all_factors",
        all_factors_generator,
        "b7c48002d0548eca9a6ae177dad9b5fcae648faecdf75c717096bafe888c7090"
    )
]

# YYY

def run_all():
    print(f"109 Python Problems tester, {version}, Ilkka Kokkarinen.")
    print("Latest version always at https://github.com/ikokkari/PythonProblems")
    try:
        if version_info < (3, 7, 0):
            print("THIS SCRIPT REQUIRES PYTHON 3.7.0 OR LATER. EXITING.")
            exit(1)
        implemented = sort_by_source()
        print(f"Student file labs109.py contains {len(implemented)} recognized functions to test.")
        if use_expected_answers:
            # If record file exists, read the expected answers from it.
            if os.path.exists(expected_answers_file):
                known, curr, verified = dict(), '', False
                with gzip.open(expected_answers_file, 'rt', encoding='utf-8') as rf:
                    storing = False
                    for line in rf:
                        line = line.strip()
                        # Special marker to indicate start of new function.
                        if line.startswith(function_prefix):
                            curr = line[len(function_prefix):]
                            storing = curr in implemented
                            known[curr] = []
                        # Special marker used to code the version information.
                        elif line.startswith(version_prefix):
                            if line[len(version_prefix):] != version:
                                print(f'VERSION MISMATCH In {expected_answers_file} !!!!!')
                                print(f'REQUIRED: {version}')
                                print(f'ACTUAL  : {line[len(version_prefix):]}')
                                exit(2)
                            else:
                                verified = True
                        elif storing:
                            known[curr].append(line)
                if not verified:  # To recognize super old versions of expected answers.
                    print(f"YOU ARE USING A VERY OBSOLETE VERSION OF {expected_answers_file}. EXITING.")
                    exit(3)
                else:
                    print(f"Finished reading expected answers.")
                    test_all_functions(labs109, known=known)
            else:
                # If the record file doesn't exist, record the model answers.
                if can_record:
                    with gzip.open(expected_answers_file, 'wt') as rf:
                        test_all_functions(labs109, recorder=rf)
                else:
                    print("You are missing the expected_answers file. Please download this file")
                    print("from the same place where you got this tester script from, to allow")
                    print("this tester to emit proper bug reports for test cases.")
                    test_all_functions(labs109)
        else:
            print("Testing functions without using recorded expected answers.")
            test_all_functions(labs109, known=None)
    except Exception as e:
        print(f"TESTER CRASHED WITH ERROR: {e}")
        exit(4)


# Given teacher and student implementations of the same function, run the
# same test cases for both of them, and output either the first or the
# shortest test case at which these two implementations disagree.

def discrepancy(teacher, student, test_generator, stop_at_first=False, print_all=False):
    shortest_args, disc_teacher, disc_student, disc, cases = None, None, None, 0, 0
    for n, args in enumerate(test_generator(fixed_seed)):
        # Turn the args into a tuple, if they aren't one already.
        if type(args) != tuple:
            args = (args,)
        current_args = stringify_args(args)
        cases += 1
        try:
            result_teacher = canonize(teacher(*args))
        except Exception as e:
            result_teacher = f"TEACHER CRASH! {e}"
        try:
            result_student = canonize(student(*args))
        except Exception as e:
            result_student = f"STUDENT CRASH! {e}"
        if result_teacher != result_student:
            disc += 1
            if stop_at_first or shortest_args is None or len(current_args) < len(shortest_args):
                shortest_args, disc_teacher, disc_student = current_args, result_teacher, result_student
            if print_all:
                print(f"Current_args: {current_args}")
                print(f"Student: {result_student}")
                print(f"Teacher: {result_teacher}")
            if stop_at_first:
                break
    if shortest_args is None:
        print("Both functions returned the same answers.")
        return True
    else:
        if stop_at_first:
            print("First discrepancy found. It was:")
        else:
            print(f"For {cases} test cases, {disc} discrepancies were found.")
            print("Shortest discrepancy input was:")
        print(shortest_args)
        print(f"Teacher: {repr(disc_teacher)}")
        print(f"Student: {repr(disc_student)}")
        return False


run_all()


# teacher student generator
#discrepancy(labs109.max_blocks, max_blocks, max_blocks_generator, print_all=True, stop_at_first=False)
