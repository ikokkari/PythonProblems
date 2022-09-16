# Automated tester for the problems in the collection
# "109 Python Problems for CCPS 109" by Ilkka Kokkarinen.
# Ilkka Kokkarinen, ilkka.kokkarinen@gmail.com

# Requires Python 3.7+ for the guarantee to iterate collections
# in the insertion order, needed to run some test case generators
# the exact same way in every platform and future Python version.

from hashlib import sha256
from time import time
from itertools import islice, permutations, zip_longest
import random
import gzip
import os.path
from sys import version_info, exit
import labs109
from fractions import Fraction

# During development, this dictionary contains the functions whose calls and
# results you want to see first during the test run. Make each entry "fname":N,
# where N is how many test cases you want to see printed out. This also makes
# the tester to run the tests for these functions first, regardless of their
# position in the labs109.py file. Use the limit of -1 to say "all test cases".

verbose_execution = {
    #   "function_one": 100,  # Print the first 100 test cases of function_one
    #   "function_two": -1,   # Print all test cases of function_two, however many there are
    #   "function_three": 0   # Be silent with function_three (but run it early)
}

# Whether to use the expected answers from the file when they exist.
use_expected_answers = True

# The release date of this version of the tester.
version = "September 16, 2022"

# Fixed seed used to generate pseudorandom numbers.
fixed_seed = 12345

# How many test cases to record in the file for each function.
testcase_cutoff = 400

# Name of the file that contains the expected answers.
expected_answers_file = 'expected_answers'

# Markers used to separate the parts of the expected answers file.
# These should never appear as the prefix of any expected answer.
version_prefix = '<$$$$>'
function_prefix = '<****>'

# Timeout cutoff for individual function tests, in seconds.
timeout_cutoff = 20

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

def stringify_args(args, cutoff=600):
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
                result += f"[{left}, <{len(a)-10} omitted...>, {right}]"
        else:
            result += repr(a) if len(repr(a)) < cutoff else '[...]'
    return result


# Given teacher and student implementations of the same function, run
# the test cases for both of them and output the first or the shortest
# test case for which these two implementations disagree.

def discrepancy(teacher, student, test_cases, stop_at_first=False):
    shortest_args, disc_teacher, disc_student, disc, cases = None, None, None, 0, 0
    for n, args in enumerate(test_cases):
        # Turn the args into a tuple, if they aren't that already.
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
            if stop_at_first:
                break
    if shortest_args is None:
        print("Both functions returned the same answers.")
        return True
    else:
        if stop_at_first:
            print("First discrepancy found. It was:")
        else:
            print(f"For {cases} test cases, found {disc} discrepancies.")
            print("Shortest discrepancy input was:")
        print(shortest_args)
        print(f"Teacher: {repr(disc_teacher)}")
        print(f"Student: {repr(disc_student)}")
        return False


# Runs the function f for its test cases, calculating SHA256 checksum
# for the results. If the checksum matches the expected, return the
# running time, otherwise return -1. If expected == None, print out
# the computed checksum instead. If recorder != None, print out the
# arguments and the result returned from function into the recorder.

def test_one_function(f, test_cases, expected_checksum=None, recorder=None, expected_answers=None):
    fname, recorded, output_len = f.__name__, None, 0
    print(f"{fname}: ", end="", flush=True)
    # How many results of function calls to print out.
    verb_count = verbose_execution.get(fname, 0)
    if recorder:
        print(f"{function_prefix}{fname}", file=recorder)
    if expected_answers:
        recorded = expected_answers.get(fname, None)
    chk, start_time, crashed = sha256(), time(), False
    for (count, test_args) in enumerate(test_cases):
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
            print(f"CRASH AT TEST CASE #{count} WITH ARGS: {test_args_string}")
            print(f"CAUGHT EXCEPTION: {e}")
            break
        # If the result is a set or dictionary, turn it into sorted list first.
        result = canonize(result)
        # Print out the argument and result, if in verbose mode.
        if verb_count > 0 or verb_count == -1:
            verb_count -= 1 if verb_count > 0 else 0
            print(f"{fname} #{count}: ", end="")
            print(test_args_string)
            print(f"RESULT: {result}")
        # Update the checksum.
        sr = str(result)
        chk.update(sr.encode('utf-8'))
        # When in recording mode, write the answer to the record file.
        if recorder:
            output = sr.strip()
            print(output, file=recorder)
            output_len += len(output) + 1
            if count >= testcase_cutoff:
                break
        if use_expected_answers and expected_answers and count < testcase_cutoff and recorded:
            if sr.strip() != recorded[count]:
                crashed = True
                print(f"DISCREPANCY AT TEST CASE #{count}: ")
                print("ARGUMENTS: ", end="")
                print(test_args_string)
                print(f"EXPECTED: {recorded[count]}")
                print(f"RETURNED: {sr}")
                break
        total_time = time() - start_time
        if total_time > timeout_cutoff:
            print(f"TIMEOUT AT TEST CASE #{count}. FUNCTION REJECTED AS TOO SLOW.")
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
            print(f"THESE AUTOMATED TEST CASES. ENSURE THAT YOUR {fname}")
            print("DOES NOT USE ANY FLOATING POINT CALCULATIONS WHOSE PRECISION")
            print("RUNS OUT ONCE THE NUMBERS INVOLVED BECOME LARGE ENOUGH.")
            return -1
    else:
        print(f"({output_len}) ", end='')
        return 0


# Sort the suite of test cases according to the order in which
# they appear in the student source code.

def sort_by_source(testcases_):
    funcs, recognized = dict(), set(f for (f, _, _) in testcases_)
    need_check = [f for (f, test, check) in testcases_ if check is None]
    with open('labs109.py', 'r', encoding='utf-8') as source:
        for (line_no, line) in enumerate(source):
            if line.startswith("def "):
                fname = line[4:line.find('(')].strip()
                if fname in funcs:
                    print(f"WARNING: MULTIPLE DEFINITION FOR {fname}")
                if fname in recognized:
                    funcs[fname] = 0 if fname in verbose_execution or fname in need_check else line_no
        testcases_.sort(key=lambda x: funcs.get(x[0], 9999999))
    return sorted(funcs.keys())


# Runs the tests for all functions in the suite, returning the
# count of how many of those were implemented and passed the test.

def test_all_functions(module, testcases_, recorder=None, known=None):
    if recorder:
        print("\nRECORDING THE RESULTS OF INSTRUCTOR MODEL SOLUTIONS.")
        print("IF YOU ARE A STUDENT, YOU SHOULD NOT BE SEEING THIS")
        print(f"MESSAGE!!! ENSURE THAT THE FILE {expected_answers_file} FROM")
        print("WHEREVER YOU DOWNLOADED THIS AUTOMATED TESTER IS ALSO")
        print("PROPERLY PLACED IN THIS VERY SAME WORKING DIRECTORY!!!\n")
    count, total = 0, 0
    if recorder:
        print(f"{version_prefix}{version}", file=recorder)
    for (fname, test_cases, expected) in testcases_:
        try:
            f = module.__dict__[fname]
        except KeyError:
            continue
        total += 1
        result = test_one_function(f, test_cases, expected, recorder, known)
        if result >= 0:
            count += 1
    if recorder:
        print("\nRecording model answers complete.")
    else:
        print(f"{count} out of {total} functions ", end="")
        print(f"of {len(testcases_)} possible work.")
    return count


# Named constants used by some test case generators.

ups = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
lows = "abcdefghijklmnopqrstuvwxyz"

__primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
            47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101]

# Some utility functions to help writing test generators.

# Produce an infinite sequence of exponentially increasing integers.
# The parameters scale and skip determine how quickly the sequence grows.


def scale_random(seed, scale, skip):
    # The seed value determines the future random sequence.
    rng = random.Random(seed)
    curr, count, orig = 1, 0, scale
    while True:
        curr += rng.randint(1, scale)
        yield curr
        count += 1
        if count == skip:
            scale = scale * orig
            count = 0


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
    count = 0
    while True:
        yield n
        count += 1
        if count == goal:
            goal, count, n = goal + inc, 0, n + 1


# The test case generators for the individual functions.

def ordinal_transform_generator(seed):
    rng, u, v = random.Random(seed), 1, 4
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
    rng = random.Random(seed)
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
    rng = random.Random(seed)
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
    yield 'z' * 10**6


def best_clubs_generator(seed):
    yield [300, 250, 200, 325, 275, 350, 225, 375, 400],
    yield [7, 11],
    yield [40, 110, 210],
    yield [2, 5, 7, 10, 14],
    rng = random.Random(seed)
    m = 5
    for n in islice(pyramid(4, 40, 1), 150):
        holes = [rng.randint(1, m) for _ in range(n)]
        yield holes,
        m += 1


def illuminate_all_generator(seed):
    yield [0, 0, 0, 0, 0],
    yield [2, 0, 1, 0, 2],
    yield [2, 1, 3, 1, 2],
    rng = random.Random(seed)
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
    rng = random.Random(seed)
    for n in islice(pyramid(3, 3, 2), 2000):
        perm = [i for i in range(n)]
        rng.shuffle(perm)
        m = rng.randint(1, n-1)
        constraints = set()
        while len(constraints) < m:
            idx = sorted(rng.sample(range(n), 3))
            if rng.randint(0, 99) < 50:
                constraints.add((perm[idx[0]], perm[idx[1]], perm[idx[2]]))
            else:
                constraints.add((perm[idx[2]], perm[idx[1]], perm[idx[0]]))
        constraints = list(constraints)
        if rng.randint(0, 99) < 50:
            ci = rng.randint(0, m-1)
            con = constraints[ci]
            if rng.randint(0, 99) < 50:
                constraints[ci] = (con[1], con[0], con[2])
            else:
                constraints[ci] = (con[0], con[2], con[1])
        yield perm, constraints


def stepping_stones_generator(seed):
    rng = random.Random(seed)
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
    rng = random.Random(seed)
    for n in islice(pyramid(3, 5, 1), 600):
        aliens = set()
        x = rng.randint(0, n-1)
        y = rng.randint(0, n-1)
        m = rng.randint(max(1, n // 3), 3*n)
        while len(aliens) < m:
            aliens.add((x, y))
            if rng.randint(0, 1):
                x = rng.randint(0, n-1)
            else:
                y = rng.randint(0, n-1)
        yield n, sorted(aliens)


def cut_into_squares_generator(seed):
    rng = random.Random(seed)
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
    rng = random.Random(seed)
    for n in islice(pyramid(7, 2, 3), 5000):
        items = list(range(n))
        rng.shuffle(items)
        yield items
    # Just to make sure that you are not being a Shlemiel.
    for n in range(10**6, 0, -10**5):
        perm = list(range(n))
        perm.reverse()
        for k in range(1000):
            i1 = rng.randint(0, n-1)
            i2 = rng.randint(0, n-1)
            perm[i1], perm[i2] = perm[i2], perm[i1]
        yield perm


def domino_tile_generator(seed):
    rng = random.Random(seed)
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


def wordomino_generator():
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


def reverse_110_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(4, 5, 4), 1500):
        yield [rng.randint(0, 1) for _ in range(n)]


def candy_share_generator(seed):
    yield from [[1], [1, 0], [0, 1], [1, 0, 1], [2, 0, 0], [0, 3, 0, 0]]
    rng = random.Random(seed)
    for n in islice(pyramid(4, 2, 3), 2000):
        candies = [0 for _ in range(n)]
        remain = rng.randint(3, n-1)
        while remain > 0:
            c = min(remain, rng.randint(1, n//10 + 1))
            candies[rng.randint(0, n-1)] += c
            remain -= c
        yield candies


def leibniz_generator(seed):
    yield [1, -1, 1, -1, 1], [0, 1, 2, 3, 4]
    rng = random.Random(seed)
    n, count, goal, heads = 5, 0, 10, [1]
    for _ in range(1500):
        if goal < 30 or rng.randint(0, 99) < 50:
            e = rng.randint(-n, n)
        else:
            den = rng.randint(2, n)
            num = rng.randint(1, den - 1)
            sign = rng.choice([-1, 1])
            e = Fraction(sign * num, den)
        heads.append(e)
        if len(heads) > 3:
            p = rng.randint(1, min(10, len(heads) // 2))
            pos = rng.sample(range(len(heads)), p)
            yield heads, pos
        count += 1
        if count == goal:
            count, goal, n, heads = 0, goal + 1, n + 1, []


def prominences_generator(seed):
    yield from [[42], [0], [1, 3, 1], [3, 1, 4], [1, 10, 5, 20, 6, 10, 4]]
    yield [3, 10, 9, 8, 7, 6, 5, 4, 3, 11, 1]

    # Permutations up to length 6 ought to root out most logic errors.
    for k in range(1, 7):
        for p in permutations(range(1, k+1)):
            yield list(p)

    # Okay, basic logic seems right, so on to pseudorandom fuzz testing.
    rng = random.Random(seed)
    scale, n, count, goal = 3, 7, 0, 10
    for _ in range(5000):
        height, change = [rng.randint(1, scale)], +1
        while len(height) < n:
            if rng.randint(0, 99) < 40:
                change = -change
            ee = max(1, height[-1] + change * rng.randint(1, scale))
            ee = ee if ee != height[-1] else ee + 1
            height.append(ee)
        while height[-1] > scale:
            height.append(height[-1] - rng.randint(1, scale))
        yield height
        count += 1
        if count == goal:
            count, goal, scale, n = 0, goal + 4, scale + 2, n + 1


def brussels_choice_step_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(1, 5, 10), 1000):
        num = random_int(rng, n, 40)
        nn = len(str(num))
        a = rng.randint(1, nn)
        b = rng.randint(1, nn)
        yield num, min(a, b), min(max(a, b), 2 + min(a, b))


def ryerson_letter_grade_generator():
    yield from range(0, 150)


def is_ascending_generator(seed):
    yield [1, 2, 2]    # Because students don't read instructions
    rng = random.Random(seed)
    for i in range(200):
        for j in range(10):
            items = [rng.randint(-(i+2), i+2)]
            for k in range(i + 1):
                items.append(items[-1] + rng.randint(0, 2 * i + 1))
            yield items[:]
            if i > 2:
                for k in range(rng.randint(0, 5)):
                    idx = rng.randint(1, len(items)-1)
                    items[idx-1], items[idx] = items[idx], items[idx-1]
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
    # On to fuzzing...
    rng = random.Random(seed)
    for i in range(1000):
        n = rng.randint(2, 3 + i // 50)
        pn = rng.randint(0, n + 2)
        pieces = set()
        while len(pieces) < pn:
            px = rng.randint(0, n-1)
            py = rng.randint(0, n-1)
            if (px, py) not in pieces:
                pieces.add((px, py))
        yield n, list(pieces)


def rooks_with_friends_generator(seed):
    rng = random.Random(seed)
    for (n, pieces) in safe_squares_generator(seed):
        fn = rng.randint(0, n)
        yield n, pieces[:fn], pieces[fn:]
        yield n, pieces[fn:], pieces[:fn]


def first_preceded_by_smaller_generator(seed):
    rng = random.Random(seed)
    scale = 3
    for n in islice(pyramid(3, 3, 2), 1000):
        items = [rng.randint(0, n)]
        for _ in range(n):
            items.append(items[-1] + rng.randint(0, scale))
        rng.shuffle(items)
        yield items, rng.randint(1, n//2)
        scale += 1


def count_and_say_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(2, 3, 2), 2000):
        for p in [30, 50, 90]:
            yield str(random_int(rng, n, p))


def reverse_ascending_sublists_generator(seed):
    rng = random.Random(seed)
    s, p = 3, 50
    for n in islice(pyramid(3, 5, 3), 2000):
        d, items = rng.choice([-1, +1]), [rng.randint(-s, s)]
        for _ in range(n-1):
            items.append(items[-1] + d * rng.randint(1, s))
            d = -d if rng.randint(0, 99) < p else d
        yield items
        s, p = s + 1, (p+3) % 100


def give_change_generator(seed):
    rng = random.Random(seed)
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
                yield amount, use
                amount += rng.randint(1, 2 + 2 * amount // 3)


suits = ['clubs', 'diamonds', 'hearts', 'spades']
ranks = {'two': 2, 'three': 3, 'four': 4, 'five': 5,
         'six': 6, 'seven': 7, 'eight': 8, 'nine': 9,
         'ten': 10, 'jack': 11, 'queen': 12, 'king': 13,
         'ace': 14}

deck = [(rank, suit) for suit in suits for rank in ranks.keys()]


def bridge_hand_generator(seed):
    rng = random.Random(seed)
    ranks_list = [r for r in ranks]
    for n in range(3000):
        flip_prob = 10 + 10 * (n % 8)
        hand = set()
        suit = rng.choice(suits)
        rank = rng.choice(ranks_list)
        while len(hand) < 13:
            hand.add((rank, suit))
            if rng.randint(0, 99) < flip_prob:
                suit = rng.choice(suits)
            rank = rng.choice(ranks_list)
        yield list(hand),


def winning_card_generator(seed):
    rng = random.Random(seed)
    for _ in range(10000):
        hand = rng.sample(deck, 4)
        for trump in suits:
            yield hand[:], trump
        yield hand[:], None


def hand_shape_distribution_generator(seed):
    rng = random.Random(seed)
    for i in range(2, 50):
        hands = [rng.sample(deck, 13) for _ in range(i * i)]
        yield hands


def milton_work_point_count_generator(seed):
    for hand in bridge_hand_generator(seed):
        hand = hand[0]
        for suit in suits:
            yield hand, suit
        yield hand, 'notrump'


def possible_words_generator(seed):
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    rng = random.Random(seed)
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
    rng = random.Random(seed)
    for n in islice(pyramid(2, 10, 10), 1000):
        exp, count = [], 0
        while len(exp) < n or count != 1:
            if count > 1 and (count > 10 or rng.randint(0, 99) < 50):
                exp.append(rng.choice(['+', '-', '*', '/']))
                count -= 1
            else:
                exp.append(rng.randint(1, 10))
                count += 1
        yield exp


def expand_intervals_generator(seed):
    yield ''
    rng = random.Random(seed)
    for j in range(200):
        curr, result, first = 0, '', True
        n = rng.randint(1, 3 + j // 50)
        for _ in range(n):
            if not first:
                result += ','
            first = False
            if rng.randint(0, 99) < 20:
                result += str(curr)
                curr += rng.randint(2, 10)
            else:
                end = curr + rng.randint(1, 30)
                result += f"{curr}-{end}"
                curr = end + rng.randint(2, 10)
        yield result


def collapse_intervals_generator(seed):
    yield from [[], [42], [1, 2], [1, 3]]
    rng = random.Random(seed)
    for n in islice(pyramid(3, 3, 1), 1000):
        curr = rng.randint(1, n)
        items = []
        for _ in range(n):
            items.append(curr)
            if rng.randint(0, 99) < max(5, 20 - n//2):
                curr += rng.randint(2, n)
            else:
                curr += 1
        yield items


def __no_repeated_digits(n, allowed):
    n = str(n)
    for i in range(4):
        if n[i] not in allowed:
            return False
        for j in range(i+1, 4):
            if n[i] == n[j]:
                return False
    return True


def bulls_and_cows_generator(seed):
    rng = random.Random(seed)
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
                if not(bulls == 3 and cows == 1):  # impossible
                    result.append((guess, bulls, cows))
        yield result


def can_balance_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(3, 4, 3), 1000):
        items, moms, s = [[], []], [0, 0], 2*n
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
    yield from islice(scale_random(seed, 3, 6), 2000)


def josephus_generator(seed):
    rng = random.Random(seed)
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
    yield 0    # Important edge case
    for v in islice(scale_random(seed, 3, 10), 2000):
        yield v
        yield -v


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


def brangelina_generator():
    n = len(__names)
    for i in range((n * (n-1)) // 2):
        first = __names[i % n]
        second = __names[(i + i // n + 1) % n]
        yield first, second


def frequency_sort_generator(seed):
    rng = random.Random(seed)
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
    rng = random.Random(seed)
    for n in range(0, 300, 2):
        base = rng.randint(2, 3 + n // 4)
        exp = rng.randint(2, 3 + n // 10)
        off = rng.choice([0, 0, -1, +1])
        yield base ** exp - off


def sort_by_digit_count_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(1, 3, 1), 1000):
        items = []
        for _ in range(n):
            d = rng.randint(1, n + 3)
            items.append(random_int(rng, d, 50))
        yield items


def count_divisibles_in_range_generator(seed):
    prev = 0
    vals = islice(scale_random(seed, 2, 6), 1000)
    divs = islice(scale_random(seed, 2, 20), 1000)
    for (v, d) in zip(vals, divs):
        yield prev, v, d
        yield -prev, v, d
        prev = v


def losing_trick_count_generator(seed):
    rng = random.Random(seed)
    for _ in range(10000):
        yield rng.sample(deck, 13)


def riffle_generator(seed):
    rng = random.Random(seed)
    for i in range(50):
        items = [rng.randint(-i*i, i*i) for _ in range(2 * i)]
        yield items[:], True
        yield items, False


def words_with_given_shape_generator():
    patterns = [  # Tactically chosen patterns to give reasonably short answers
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
        words = [x.strip() for x in f]

    for pattern in patterns:
        yield words, pattern


def squares_intersect_generator(seed):
    rng = random.Random(seed)
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
    rng = random.Random(seed)
    for i in range(3000):
        n = rng.randint(0, 9)
        p = 1
        one_more = True
        for j in range(1 + i // 10):
            yield n
            yield n+p
            p = p * 10
            if not one_more:
                break
            if rng.randint(0, 99) < 95:
                n = 10 * n + rng.choice([1, 3, 5, 7, 9])
            else:
                n = 10 * n + rng.choice([0, 2, 4, 6, 8])
                one_more = False


def lattice_paths_generator(seed):
    rng = random.Random(seed)
    yield 2, 2, [(1, 0), (0, 1)]
    yield 5, 5, [(4, 5), (5, 4)]
    for n in islice(pyramid(2, 3, 2), 1000):
        x = n + rng.randint(0, 3)
        y = n + rng.randint(0, 3)
        tabu = set()
        m = rng.randint(n, 2*n)
        while len(tabu) < m:
            xx, yy = x, y
            while (xx, yy) == (x, y) or (xx, yy) == (0, 0):
                xx = rng.randint(0, x)
                yy = rng.randint(0, y)
            tabu.add((xx, yy))
        yield x, y, list(tabu)


def count_carries_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(3, 5, 1), 5000):
        nums = []
        for _ in range(2):
            m = 0
            for _ in range(rng.randint(n // 2, n)):
                if rng.randint(0, 99) < 80:
                    m = 10 * m + rng.randint(5, 9)
                else:
                    m = 10 * m + rng.randint(0, 4)
            nums.append(m)
        yield nums[0], nums[1]


def count_squares_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(3, 5, 3), 300):
        pts = set()
        while len(pts) < 2 * n:
            x = rng.randint(0, n)
            y = rng.randint(0, n)
            pts.add((x, y))
            if rng.randint(0, 99) < 40:
                dx = rng.randint(1, n)
                dy = rng.randint(-3, n)
                pts.add((x+dx, y+dy))
                pts.add((x+dy, y-dx))
                pts.add((x+dx+dy, y-dx+dy))
        yield sorted(pts)


def three_summers_generator(seed):
    rng = random.Random(seed)
    count, goal = 0, 1
    items = []
    for i in range(200):
        count += 1
        if count == goal:
            count, goal = 0, goal + 5
            items = [rng.randint(1, 2 + i)]
        items.append(items[-1] + rng.randint(1, 2 + i*i))
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
    yield from ['d', 'uuddd', 'ddd', 'udud', 'uduuudddd']
    rng = random.Random(seed)
    for i in range(15000):
        if rng.randint(0, 99) < 50:
            c = rng.randint(1, 2 + 10 * i)
            pat = []
            while c > 1:
                if c % 2 == 0:
                    c = c // 2
                    pat.append('d')
                else:
                    c = 3 * c + 1
                    pat.append('u')
        else:
            len_ = rng.randint(1, min(100, 2 + i // 1000))
            pat = [('u' if (rng.randint(0, 99) < 50) else 'd') for _ in range(len_)]
            pat.extend(['d', 'd', 'd', 'd'])
        yield ''.join(pat)


def sum_of_two_squares_generator(seed):
    yield from islice(scale_random(seed, 2, 5), 150)


def sum_of_distinct_cubes_generator(seed):
    yield from islice(scale_random(seed, 2, 5), 200)


def seven_zero_generator(seed):
    yield from [(7,), (70,), (7700,), (77770,), (7000000,)]
    yield from [(2860,), (1001,), (2**20,), (2**10 - 1,)]
    rng = random.Random(seed)
    m = 2
    for _ in range(500):
        yield m,
        m += rng.randint(1, 5)


def remove_after_kth_generator(seed):
    rng = random.Random(seed)
    count, goal, items = 0, 5, []
    for i in range(10000):
        if len(items) > 0 and rng.randint(0, 99) < 50:
            new = rng.choice(items)
            p1 = rng.randint(0, len(items) - 1)
            p2 = rng.randint(0, len(items) - 1)
            items[p1], items[p2] = items[p2], items[p1]
        else:
            new = rng.randint(-i*i, i*i + 1)
        items.append(new)
        yield items[:], rng.randint(1, 2 + i//100)
        count += 1
        if count == goal:
            count, goal, items = 0, goal + 5, []


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


def autocorrect_word_generator():
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
    n = 200
    ns = scale_random(seed, 3, 10)
    ms = scale_random(seed + 1, 3, 10)
    hs = scale_random(seed + 2, 2, 15)
    yield from islice(zip(ns, ms, hs), n)


def is_cyclops_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(1, 3, 1), 1000):
        d = rng.randint(1, n + 2)
        left = random_int(rng, d, 70)
        right = random_int(rng, d, 70)
        mid = rng.choice("00000000000123456789")
        yield int(f"{left}{mid}{right}")


def words_with_letters_generator():
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    for letters in ["smoom", "reflux", "byoam", "xxx", "aboba", "ubsub", "rentob", "whoa"]:
        yield words, letters


def extract_increasing_generator(seed):
    rng = random.Random(seed)
    count, goal, n = 0, 4, 3
    for i in range(1000):
        digits = "".join([rng.choice('0123456789') for _ in range(n)])
        yield digits
        count += 1
        if count == goal:
            count, goal, n = 0, goal + (1 if n % 5 == 0 else 0), n + 1


def line_with_most_points_generator(seed):
    rng = random.Random(seed)
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
        yield list(points)


def count_maximal_layers_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(1, 1, 1), 2000):
        points = set()
        while len(points) < n:
            x = rng.randint(-3 - n, 3 + n)
            y = rng.randint(-3 - n, 3 + n)
            points.add((x, y))
        points = list(points)
        yield points


def taxi_zum_zum_generator(seed):
    rng = random.Random(seed)
    poss = ['L', 'R', 'F']
    moves = []
    goal, count = 5, 0
    for _ in range(3000):
        count += 1
        if count == goal:
            count, goal = 0, goal + 2
            moves = []
        else:
            moves.append(rng.choice(poss))
        yield ''.join(moves)


def count_growlers_generator(seed):
    rng = random.Random(seed)
    animals = []
    goal, count = 5, 0
    for _ in range(5000):
        count += 1
        if count == goal:
            count, goal = 0, goal + 2
            animals = []
        animals.append(rng.choice(['cat', 'tac', 'dog', 'god']))
        yield animals[:]


def tukeys_ninthers_generator(seed):
    rng = random.Random(seed)
    n, items, goal, step = 0, [1], 1, 0
    for i in range(1000):
        yield items[:]
        step += 1
        if step == goal:
            step, goal = 0, goal * 3
            n += 1
            items, c = [], 0
            r = (i // 100)**2 + 2
            for _ in range(3**n):
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
    rng = random.Random(seed)
    for n in islice(pyramid(8, 3, 1), 1000):
        pieces = set()
        a, b = max(2, (n*n)//8), max(3, (n*n)//3)
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
    rng = random.Random(seed)
    for a in range(200):
        b = rng.randint(1, a + 5)
        yield a, b


def nearest_smaller_generator(seed):
    rng = random.Random(seed)
    scale = 3
    for n in islice(pyramid(1, 2, 1), 2000):
        yield [rng.randint(-scale, scale) for _ in range(n)]
        scale += 1


def domino_cycle_generator(seed):
    rng = random.Random(seed)
    for _ in range(10000):
        tiles = []
        cycle = rng.randint(0, 99) < 50
        for j in range(10):
            yield tiles[:]
            if cycle or rng.randint(0, 99) < 90:
                if len(tiles) > 0:
                    a = tiles[-1][-1]
                else:
                    a = rng.randint(1, 6)
            else:
                a = rng.randint(1, 6)
            tiles.append((a, rng.randint(1, 6)))


def van_eck_generator(seed):
    yield from islice(scale_random(seed, 3, 4), 40)


def unscramble_generator(seed):
    rng = random.Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    count = 0
    while count < 250:
        w = rng.choice(words)
        if 2 < len(w) < 9:
            first, mid, last = w[0], list(w[1:-1]), w[-1]
            rng.shuffle(mid)
            yield words, first + "".join(mid) + last
            count += 1


def crag_score_generator():
    for d1 in range(1, 7):
        for d2 in range(1, 7):
            for d3 in range(1, 7):
                yield [d1, d2, d3]


def midnight_generator(seed):
    rng = random.Random(seed)
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


def substitution_words_generator():
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    for pattern in ["LLRR", "ABACAB", "NONONO", "WW", "HEYYEAH", "YAHHAY", "RAUMAA", "INTELLIGENCE",
                    "MELANCHALL", "MELLEMOSS", "ONOOBB", "AOOA", "INNAAN", "GOLOGG", "ECEC"]:
        yield pattern, words


def count_dominators_generator(seed):
    rng = random.Random(seed)
    items = []
    count, goal = 0, 10
    for _ in range(20000):
        yield items[:]
        count += 1
        if count == goal:
            count, goal = 0, goal + 2
            items = []
        r = (goal - count)**3
        items.append(rng.randint(-r, r))
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
    rng = random.Random(seed)
    for i in range(40):
        rolls = []
        while len(rolls) < 2 + (i % 5):
            dice = tuple([rng.randint(1, 6) for _ in range(3)])
            rolls.append(dice)
            if rng.randint(0, 99) < 20:
                rolls.append(rng.choice(rolls))
        yield rolls


def bulgarian_solitaire_generator(seed):
    rng = random.Random(seed)
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
    rng = random.Random(seed)
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
    rng = random.Random(seed)
    count, goal, prog, n = 0, 5, [], 1
    for i in range(500):
        num = rng.randint(1, 10 + i)
        den = rng.randint(1, 10 + i)
        prog.append((num, den))
        k = rng.randint(0, len(prog) - 1)
        prog[k], prog[-1] = prog[-1], prog[k]
        n = rng.randint(2, 10)
        yield n, prog[:], 10
        count += 1
        if count == goal:
            count, goal, prog = 0, goal + 1, []


def scylla_or_charybdis_generator(seed):
    rng = random.Random(seed)
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
    rng = random.Random(seed)
    count, goal, max_r = 0, 5, 10
    for n in range(1, 250, 2):
        d = 40 * n
        disks = set()
        while len(disks) < 10 * n:
            x = rng.randint(-d, d)
            y = rng.randint(-d, d)
            r = rng.randint(1, max_r)
            disks.add((x, y, r))
        disks = list(disks)
        yield disks
        count += 1
        if count == goal:
            count, goal = 0, goal + 2
            max_r += 5


def arithmetic_progression_generator(seed):
    rng = random.Random(seed)
    m = 5
    for i in range(150):
        elements = set()
        for _ in range(m):
            start = rng.randint(1, i*i + 3)
            step = rng.randint(1, 100)
            for k in range(rng.randint(1, 10)):
                elements.add(start + k * step)
        yield sorted(elements)
        if i % 10 == 0:
            m += 1


def cookie_generator(seed):
    rng = random.Random(seed)
    for i in range(25):
        items = [rng.randint(1, 2 + i)]
        for j in range(3 + i // 7):
            items.append(items[-1] + rng.randint(1, 2 + i))
        yield items


def eliminate_neighbours_generator(seed):
    for n in range(1, 7):
        for p in permutations(range(1, n + 1)):
            yield list(p)
    rng = random.Random(seed)
    count, goal = 0, 1
    items, m = [1, 2, 3, 4, 5, 6, 7], 7
    for i in range(2000):
        yield items[:]
        count += 1
        if count == goal:
            count, goal = 0, goal + 3
            m = 8 + i // 50
            items = list(range(1, m))
        items.append(m)
        m += 1
        j = rng.randint(0, len(items) - 1)
        items[j], items[-1] = items[-1], items[j]
    for n in range(100, 1501):
        items = [i+1 for i in range(n)]
        i1 = rng.randint(0, n//2)
        i2 = rng.randint(0, n//2)
        items[i1], items[i2] = items[i2], items[i1]
        yield items[:]
        yield list(reversed(items))


def counting_series_generator(seed):
    yield from islice(scale_random(seed, 5, 2), 1000)


def __zigzag(rng, len_, prob):
    curr = rng.randint(1, 8)
    d = rng.choice([+1, -1])
    for _ in range(len_):
        last = curr % 10
        dd = d if rng.randint(1, 100) < prob else -d
        if dd == +1 and last > 0:
            n = rng.randint(0, last - 1)
        elif dd == -1 and last < 9:
            n = rng.randint(last + 1, 9)
        else:
            n = rng.randint(0, 9)
        curr = curr * 10 + n
        d = -d
    return curr


def is_zigzag_generator(seed):
    rng = random.Random(seed)
    for _ in range(100):
        for j in range(20):
            curr = __zigzag(rng, j, 10)
            yield curr


def wythoff_array_generator(seed):
    rng = random.Random(seed)
    curr, step = 1, 1
    for _ in range(150):
        yield curr
        curr += rng.randint(1, 4 * step)
        step += 1


def hourglass_flips_generator(seed):
    rng = random.Random(seed)
    for _ in range(50):
        glasses, curr = [], rng.randint(6, 11)
        for j in range(rng.randint(2, 4)):
            low = 0 if rng.randint(0, 99) < 60 else rng.randint(5, max(6, curr // 2))
            glasses.append((curr, low))
            curr += rng.randint(1, 5)
        t = rng.randint(curr + 2, 2 * curr)
        yield glasses, t


def knight_jump_generator(seed):
    rng = random.Random(seed)
    for i in range(10000):
        k = 2 + (i % 50)
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
    rng = random.Random(seed)
    count = 0
    while count < 5000:
        c = [rng.randint(-10, 10) for _ in range(6)]
        if c[2:4] == c[4:6] or c[2:4] == [0, 0] or c[4:6] == [0, 0]:
            continue
        t = rng.randint(1, 2 + 2**(count // 100))
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
            count += 1


def spread_the_coins_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(5, 3, 2), 500):
        coins = [0 for _ in range(n)]
        coins[-1] = 1
        m = rng.randint(2*n, 3*n)
        while m > 0:
            c = rng.randint(1, 4)
            i = rng.randint(0, n-1)
            coins[i] += c
            m -= c
        u = rng.randint(2, 2 + max(coins) // 2)
        left = rng.randint(1, u - 1)
        yield coins, left, u-left


def group_and_skip_generator(seed):
    rng = random.Random(seed)
    for n in islice(scale_random(seed, 2, 10), 400):
        b = rng.randint(1, max(2, n // 100))
        a = rng.randint(b+1, 2*b+1)
        yield n, a, b


def nearest_polygonal_number_generator(seed):
    rng = random.Random(seed)
    yield from [(7, 3), (7, 4), (8, 3), (10, 9), (12, 4), (15, 6), (19, 7)]
    curr = 20
    for i in range(250):
        for j in range(15):
            curr = curr + rng.randint(1, curr // 10)
            s = rng.randint(3, i + 3)
            yield curr, s
        curr = curr * 2


def subtract_square_generator(seed):
    rng = random.Random(seed)
    for i in range(1, 9):
        curr = rng.randint(1, 10)
        query = []
        for j in range(2 * i):
            query.append(curr)
            curr = (4 * curr) // 3 + rng.randint(1, max(3, curr // 3))
        yield query


def perimeter_limit_split_generator(seed):
    rng = random.Random(seed)
    for a in range(10, 100):
        b = rng.randint(1, a)
        p = rng.randint(5, 3 * a)
        yield (a, b, p) if rng.randint(0, 1) else (b, a, p)


def duplicate_digit_bonus_generator(seed):
    rng = random.Random(seed)
    n, count, goal = 1, 0, 5
    for _ in range(3000):
        yield random_int(rng, n, 60)
        count += 1
        if count == goal:
            count, goal, n = 0, goal + 5, n + 1


def hitting_integer_powers_generator(seed):
    rng = random.Random(seed)
    for n in islice(pyramid(2, 5, 10), 100):
        pn = __primes[:n]
        a = rng.choice(pn)
        b = rng.choice(pn)
        for p in __primes[:n]:
            if rng.randint(0, 99) < 20:
                a = a * p
            if rng.randint(0, 99) < 20:
                b = b * p
        yield a, b, 10**(rng.randint(1, min(4, n)))


def permutation_cycles_generator(seed):
    # All permutations up to length 5
    for n in range(1, 6):
        for p in permutations(range(n)):
            yield list(p)
    # Fuzz test some of the longer permutations
    rng = random.Random(seed)
    for n in islice(pyramid(6, 2, 3), 1000):
        for _ in range(n//2):
            perm = list(range(n))
            rng.shuffle(perm)
            yield perm


def word_height_generator(seed):
    rng = random.Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    for _ in range(5000):
        idx = rng.randint(0, len(words) - 1)
        yield words, words[idx]


def mcculloch_generator(seed):
    rng = random.Random(seed)
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
    rng = random.Random(seed)
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


def is_left_handed_generator():
    for a in range(1, 5):
        for b in range(a + 1, 6):
            for c in range(b + 1, 7):
                if a+b != 7 and a+c != 7 and b+c != 7:
                    yield from ((p,) for p in permutations([a, b, c]))


def balanced_centrifuge_generator(seed):
    rng = random.Random(seed)
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
    rng = random.Random(seed)
    k, goal = 2, 10
    for i in range(5000):
        to_sow = rng.randint(0, 6 * k * k * k * k)
        sown = 0
        board = [0 for _ in range(2 * k)]
        while sown*sown < to_sow:
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


def conjugate_regular_generator():
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

    rng = random.Random(seed)
    count, goal, nn, aliens, n, m = 0, 1, 7, [], 0, 0
    for _ in range(5000):
        count += 1
        if count == goal:
            count, goal, nn, aliens = 0, goal + 1, nn + 1, []
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
    rng = random.Random(seed)
    count, goal, n, piles = 0, 2, 5, []
    for _ in range(300):
        piles.append(rng.randint(1, n))
        piles.append(rng.randint(1, n))
        pos = rng.randint(0, len(piles) - 1)
        piles[-1] += piles[pos]
        del piles[pos]
        yield piles[:]
        count += 1
        if count == goal:
            count, goal, n, piles = 0, goal + 2, n + 1, []
    for n in range(10, 30):
        yield [(i-1)*(i-2) for i in range(n)]


def colour_trio_generator(seed):
    rng = random.Random(seed)
    items = ''
    for n in islice(pyramid(3, 4, 1), 10000):
        items += rng.choice('ryb')
        yield items
        if len(items) == n:
            items = rng.choice('ryb')


def schmalz_generator():
    yield "Uncle Egg White and Obi-Wan Tsukenobi are the very best of the enterprising rear.",
    yield "Spread love everywhere you go. Let no one ever come to you without leaving happier.",
    yield "When you reach the end of your rope, tie a knot in it and hang on.",
    yield "Always remember that you are absolutely unique. Just like everyone else.",
    yield "Don't judge each day by the harvest you reap but by the seeds that you plant.",
    yield "The future belongs to those who believe in the beauty of their dreams.",
    yield "Tell me and I forget. Teach me and I remember. Involve me and I learn.",
    yield "The best and most beautiful things in the world cannot be seen or even touched " +\
          "— they must be felt with the heart."
    yield "It is during our darkest moments that we must focus to see the light.",
    yield "What puny mortal can comprehend the Mighty Mind of Galactus?",
    yield "To crush your enemies, to see them driven before you, and hear the lamentation of their women.",
    yield "Everything that irritates us about others can lead us to an understanding of ourselves.",
    yield "Trying to define yourself is like trying to bite your own teeth.",
    yield "Inability to accept the mystic experience is more than an intellectual handicap. Lack of " +\
          "awareness of the basic unity of organism and environment is a serious and dangerous hallucination."
    yield '“Evil” read backwards is “live.” Demon est deus inversus.”'
    yield "想像一下清晨的多維蜘蛛網，上面佈滿了露珠",
    yield "Өндөг бол эго, шувуу бол чөлөөлөгдсөн Би юм.",
    yield "Mỗi người trong chúng ta đều là một khẩu độ mà qua đó toàn bộ vũ trụ nhìn ra.",
    yield "“Ukufuna chiyani? Nchiyani chimakupangitsa iwe kuyabwa? Kodi mukufuna mutakhala bwanji?”",
    yield "Chīwit mī xyū̀ nı ch̀wng welā nī̂ thèānận læa nı k̄hṇa nī̂ k̆ mị̀mī thī̀ s̄îns̄ud læa pĕn " +\
          "ni rạn dr̒ s̄ảh̄rạb ch̀wng welā pạccubạn nận lĕk māk k̀xn thī̀ reā ca wạd dị̂ mạn k̆ h̄āy pị " +\
          "tæ̀ k̆ yạng mī xyū̀ tlxd pị"
    yield "Do not suppose, however, that we are merely a society of lotus-eaters, lolling on divans " +\
          "and cuddling lovely women."
    yield "Agus tuiscint lochtach ar fhéiniúlacht againn, gníomhaímid ar bhealach atá mí-oiriúnach dár " +\
          "dtimpeallacht nádúrtha."
    yield "Fa tsy misy fifaliana amin'ny faharetana mandrakizay. "\
          + "Irintsika fotsiny izany satria foana ny ankehitriny."


def count_troikas_generator(seed):
    yield from [[], [42], [42, 17], [17, 42], [-5, 0], [10**42]]
    scale, rng, pct, pi = 4, random.Random(seed), [30, 50, 70], 0
    for n in islice(pyramid(3, 2, 1), 6000):
        items = [rng.randint(-scale, scale)]
        for _ in range(n-1):
            items.append(rng.choice(items) if rng.randint(0, 99) < pct[pi] else rng.randint(-scale, scale))
        yield items
        scale += 1
        pi = (pi + 1) % len(pct)


def count_corners_generator(seed, slices=4000):
    rng = random.Random(seed)
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
     arithmetic_progression_generator(fixed_seed),
     "8c8a5c48d0e0f0f469e7e1e92c208cc927012815e3bfc1361479ec263bfe27eb"
    ),
    (
     "count_overlapping_disks",
     count_overlapping_disks_generator(fixed_seed),
     "58a6774be09fa37b858a375b36d5e9ce05d49eac25a5210105"
    ),
    # Removed from problem set November 26, 2021
    # (
    # "fractional_fit",
    # fractional_fit_generator(fixed_seed),
    # "856627cc444098c9386367d5f250c0e2cddbf3ef0ecec3ba11"
    # ),
    (
     "scylla_or_charybdis",
     scylla_or_charybdis_generator(fixed_seed),
     "b1536ef2e3dcfbd98ae4b1bb054358953a45702bb6767afc2bce3a28a229c54a"
    ),
    (
     "fractran",
     fractran_generator(fixed_seed),
     "5ef5b21286fe7565e53230868d4240d41224a4543122ec0d5d"
    ),
    (
     "manhattan_skyline",
     manhattan_skyline_generator(fixed_seed),
     "cfea0db5924def2f2ecf66a69ee11a079b4d6a59f15edbd3130a2c81e2477991"
    ),
    (
     "bulgarian_solitaire",
     bulgarian_solitaire_generator(fixed_seed),
     "819172713ddd3d5a8e596b249284a52b851b3f78d6a468b1672d10991c6d92af"
    ),
    (
     "sum_of_distinct_cubes",
     sum_of_distinct_cubes_generator(fixed_seed),
     "d1ed5e8a0688116c7536b01804d09378a13559a0d6a9427ddf"
    ),
    (
     "tukeys_ninthers",
     tukeys_ninthers_generator(fixed_seed),
     "801d96631e1064d6bd8903f3e716bb397fa1c785877ee4e903"
    ),
    (
     "optimal_crag_score",
     optimal_crag_score_generator(fixed_seed),
     "5cf0e2ae4582c041343a113fcd4cb413c27f44ee8f4fafc6b3"
    ),
    (
     "count_dominators",
     count_dominators_generator(fixed_seed),
     "c9c7ad7be22449a5863277c28eb5bf0f85ecddbb76fac6d0f12a2cd65309dd67"
    ),
    # Removed from problem set December 9, 2021
    # (
    #  "forbidden_substrings",
    #  forbidden_substrings_generator(),
    #  "6174fc0fd7c0c5b2a9bcb99a82799736ea3ab2f5f1525b8c10"
    # ),
    (
     "substitution_words",
     substitution_words_generator(),
     "4cf3cd3ba0607db9ba11ec0e240391bc1e78ad62edb541d260"
    ),
    (
     "taxi_zum_zum",
     taxi_zum_zum_generator(fixed_seed),
     "decec6801d0e4c4a717503a677e725b16cad906ab9ea349000"
    ),
    (
     "midnight",
     midnight_generator(fixed_seed),
     "92890d7f13631c829d087322d0b3e6764b81063256c026ab3f9a00ae9372f963"
    ),
    (
     "crag_score",
     crag_score_generator(),
     "ea62d9694e079b948a8b622c8f6dfd2aeebddeebc59c575721"
    ),
    (
     "unscramble",
     unscramble_generator(fixed_seed),
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
     van_eck_generator(fixed_seed),
     "2938012254caba60ec8e648da870e1456d2347ea0769b8accb3c4631566f740b"
    ),
    (
     "domino_cycle",
     domino_cycle_generator(fixed_seed),
     "a584eae620badb493239fd0bebbfa7c8c17c12b3bc0f53f873"
    ),
    # Removed from problem set August 10, 2021
    # (
    # "double_trouble",
    #  double_trouble_generator(fixed_seed),
    # "49f103a7ad2c26d800d61e8645f967408a18c37cc6303a9dfc"
    # ),
    (
     "nearest_smaller",
     nearest_smaller_generator(fixed_seed),
     "d259c1784dd83540886391a148a17f36a97742514d7ad7cdaf1168a44a798e91"
    ),
    (
     "collatzy_distance",
     collatzy_distance_generator(fixed_seed),
     "ff638c3269c9418841d6a7f0ecf0fadb0ed02677f3b56078e09ede7ec0384f63"
    ),
    (
     "max_checkers_capture",
     max_checkers_capture_generator(fixed_seed),
     "1547f0eb0829ff5882178f480e8c5d24f016c5c1d95038b898f17c073c3913ee"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "bridge_score",
    # bridge_score_generator(),
    # "1d1e3f4be9fec5fd85d87f7dcfa8c9e40b267c4de49672c65f"
    # ),
    # Removed from problem set April 20, 2020
    # (
    # "minimize_sum",
    # minimize_sum_generator(seed),
    # "7e6257c998d5842ec41699b8b51748400a15e539083e5a0a20"
    # ),
    (
     "count_growlers",
     count_growlers_generator(fixed_seed),
     "3f96234a4b959581978facb1a8f44f732b5af745be4685fc96"
    ),
    # Removed from problem set August 10, 2020
    # (
    #  "kempner",
    #  kempner_generator(),
    #  "dfbf6a28719818c747e2c8e888ff853c2862fa8d99683c0815"
    # ),
    (
     "words_with_letters",
     words_with_letters_generator(),
     "2bb1d006c2549038711d9d61b96d551865662872f58ffb58fe"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "count_distinct_lines",
    # count_distinct_lines_generator(seed),
    # "c79db2f41e798a652e3742ef2a2b29801f0b3e52f4e285aa4e"
    # ),
    (
     "line_with_most_points",
     line_with_most_points_generator(fixed_seed),
     "ac302ea22f9048a164250de421969fe32a19aeb7dbf730a86f2a6c3673f8896a"
    ),
    (
     "count_maximal_layers",
     count_maximal_layers_generator(fixed_seed),
     "950e939df6b497881a6a3dea3c2a92ac5362ff2aee2841801da38eb45867902c"
    ),
    # Removed from problem set October 29, 2021
    # (
    # "square_follows",
    # square_follows_generator(fixed_seed),
    # "e571beecc69a7ac9235ba8911deef92b367e1badb9cff87f58"
    # ),
    (
     "extract_increasing",
     extract_increasing_generator(fixed_seed),
     "5d90c3ef3e0e053195ffbcc5eef3b7656b73b5c73be5019080"
    ),
    (
     "is_cyclops",
     is_cyclops_generator(fixed_seed),
     "e66d296baa3ec9b7059161bce710d5a10140a1b1e6987a73c359a8289ffc1d36"
    ),
    (
     "pyramid_blocks",
     pyramid_blocks_generator(fixed_seed),
     "9f988a1fc97c7cd92e7d358b7dd161d311c9094c66e1c78d3d"
    ),
    (
     "autocorrect_word",
     autocorrect_word_generator(),
     "93742a7a15938b9184bf93cc493699b49ff8bfe07529e42d58"
    ),
    (
     "remove_after_kth",
     remove_after_kth_generator(fixed_seed),
     "3b89af0dce7e41c2fc6a851e4a35bb76f8845c5f6929ba6ade"
    ),
    (
     "seven_zero",
     seven_zero_generator(fixed_seed),
     "2f0c5d3a4246fca6c16b13fccadcfb77f8f75a3bf417c818a24d1e21d77d2183"
    ),
    # Removed from problem set December 10, 2020
    # (
    #  "count_distinct_sums_and_products",
    #  count_distinct_sums_and_products_generator(seed),
    #  "b75370cf5c3d2c307585937311af34e8a7ad44ea82c032786d"
    # ),
    (
     "sum_of_two_squares",
     sum_of_two_squares_generator(fixed_seed),
     "93086670c2c63510741e58329a83fe42cc469762ca26c74130"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "scrabble_value",
    # scrabble_value_generator(seed),
    # "b8b08a8a1a5fd687c49c5f7147fd35bc16d4c3ac88328ada64"
    # ),
    (
     "reverse_vowels",
     schmalz_generator(),
     "710c6fd22a900fd2153d51f334568ccdf29a2863c63b2651f8"
    ),
    (
     "riffle",
     riffle_generator(fixed_seed),
     "a4dc0ce811a97e4a1f66953f10c7b04ed339cba4273c3b5deb"
    ),
    (
     "ztalloc",
     ztalloc_generator(fixed_seed),
     "b570cd16dec9233f324d34de8aa87084700f334c3e4cb17fe3660168ebdb0eff"
    ),
    (
     "losing_trick_count",
     losing_trick_count_generator(fixed_seed),
     "814fa798f0de0d1c847b0622fc21a88047d19e427ebe1d16cf"
    ),
    (
     "postfix_evaluate",
     postfix_evaluate_generator(fixed_seed),
     "47fb1c90b9198315bd27fb26ab2a7b3ca99d8e94e05f12c93d9594aa68089dd6"
    ),
    (
     "three_summers",
     three_summers_generator(fixed_seed),
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
    # tribonacci_generator(),
    # "ac64825e938d5a3104ea4662b216285f05a071cde8fd82c6fd"
    # ),
    (
     "count_squares",
     count_squares_generator(fixed_seed),
     "cb1021c7a7e1cea05e4eb7b861df761e0d9fe94c03297f2b937726aa2f14f4d6"
    ),
    (
     "count_carries",
     count_carries_generator(fixed_seed),
     "546a3962273c5c74c8d844b95d6080c48155090d467142d8c73a5450276d0caf"
    ),
    (
     "lattice_paths",
     lattice_paths_generator(fixed_seed),
     "5aab78160181125a6944933dbe70acde133ae2a739798a0ce7abfb9596a28436"
    ),
    # Removed from problem set September 16, 2022
    # (
    #  "pancake_scramble",
    #  pancake_scramble_generator(fixed_seed),
    #  "98fb3c9e30908ea6c2654d64d3c68ca2538927be529d75ddfe"
    # ),
    (
     "only_odd_digits",
     only_odd_digits_generator(fixed_seed),
     "24d656750cff73ad12fa9ff8320bbae662c2fbb5a6f4ece514"
    ),
    (
     "squares_intersect",
     squares_intersect_generator(fixed_seed),
     "fb5f90845deddea1350fa81af5a228b18a2f4922f21ce36f725d54329b89c58f"
    ),
    (
     "rooks_with_friends",
     rooks_with_friends_generator(fixed_seed),
     "5c2156612b95bda73b221fdd1ca77773f6e01108b9c48ba40437e56328b9db04"
    ),
    (
     "safe_squares_rooks",
     safe_squares_generator(fixed_seed),
     "9e06a8a2766ab41420ded02e2e2ad4fc8b03138ab38992d530296431ac8d30b5"
    ),
    (
     "safe_squares_bishops",
     safe_squares_generator(fixed_seed),
     "71e6e56c9f044b66871de3b232bdafb2af5ffba99319d8fdc60de94f5e8735ee"
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
     count_and_say_generator(fixed_seed),
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
     first_preceded_by_smaller_generator(fixed_seed),
     "7d123860240c7b8614de16f232213a81568ffd167b7cb4e8de70d6fc943dc240"
    ),
    (
     "words_with_given_shape",
     words_with_given_shape_generator(),
     "ca32049370fa695f67ebed20a4a9c7dd72cde739b637cc38e71eb8c7c699fde4"
    ),
    # Removed from problem set August 10, 2020
    # (
    #  "prime_factors",
    #  prime_factors_generator(seed),
    #  "fbb31e68d216d7430c47a3e3ac9eb0d4240ef2ae698eb2ded4"
    # ),
    (
     "fibonacci_sum",
     fibonacci_sum_generator(fixed_seed),
     "e7058a191e5dbc3a8f69f302fa5f6180e8b4d4c688f6028792576010dcb3c16b"
    ),
    # Removed from the problem set August 10, 2021
    # (
    #  "factoring_factorial",
    #  factoring_factorial_generator(fixed_seed),
    #  "be5d5249b396c259bde5338de73ae4d29831314d6c0fb9e369"
    #  ),
    (
     "bridge_hand_shorthand",
     bridge_hand_generator(fixed_seed),
     "c6beb2fd767be441a88b1869f7cdcbae9a6b232c07165e790483bf1fe57ac699"
    ),
    (
     "milton_work_point_count",
     milton_work_point_count_generator(fixed_seed),
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
     count_divisibles_in_range_generator(fixed_seed),
     "fda3d00830ff01a611eaf78401459f7ce5550596bc9b98b448"
    ),
    (
     "sort_by_digit_count",
     sort_by_digit_count_generator(fixed_seed),
     "6015a1e6aee7d3fb5f49e780a3dd935c9ffb70d7d082e75f070b714c43b7e8d8"
    ),
    (
     "is_perfect_power",
     is_perfect_power_generator(fixed_seed),
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
     frequency_sort_generator(fixed_seed),
     "7cf98bb630901b746d4765edaaea5d5d2ea011e1271c7214111a52c9725fe8fd"
    ),
    # Removed from problem set September 14, 2022
    # (
    #  "count_consecutive_summers",
    #  count_consecutive_summers_generator(),
    #  "3ade63a194b40ff5aa1b53642eee754d30f2ab48ef77330540"
    # ),
    (
     "brangelina",
     brangelina_generator(),
     "f864cef7d1d71768b2efa0334e963d517290440401d98a8e85e71134a7e12c1f"
    ),
    (
     "balanced_ternary",
     balanced_ternary_generator(fixed_seed),
     "5911fc03a906dc474c0d6dc168036610b0a81de5f61477d0eb"
    ),
    (
     "josephus",
     josephus_generator(fixed_seed),
     "6c39a1339f51ec7b8a29cf0a27636b6ba6be7527b75e89bac9"
    ),
    # Removed from problem set December 17, 2020
    # (
    #  "aliquot_sequence",
    #  aliquot_sequence_generator(),
    #  "17f910bff400bb0305e94c79e27fda857c5723385d73f2ccc4"
    # ),
    # Removed from problem set April 20, 2020
    # (
    # "all_cyclic_shifts",
    # all_cyclic_shifts_generator(),
    # "1d06f1ef0547d8441800f2dc19aa430396a0f2e8bc414e6775"
    # ),
    (
     "fibonacci_word",
     fibonacci_word_generator(fixed_seed),
     "b6385c1cb1a88f2392f507cae3bc302c468d5747af8802e410"
    ),
    # Removed from problem set September 1, 2021
    # (
    # "create_zigzag",
    # create_zigzag_generator(fixed_seed),
    # "6495896d5e3f0ed9c7f924b9f8c5c99a78700b1a5a1a6f8f98"
    # ),
    (
     "calkin_wilf",
     calkin_wilf_generator(fixed_seed),
     "fd39bebe2f409e102aa1ca8de00d520ad8d3ec9f1af9a1ad0ddcc0c4721c05d5"
    ),
    (
     "can_balance",
     can_balance_generator(fixed_seed),
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
     bulls_and_cows_generator(fixed_seed),
     "e00ca4cd1996a51ef5cd5588a7facd0a00f2e3f3946d5f4e96"
    ),
    # Removed from problem set October 21, 2021
    # (
    # "recaman",
    # recaman_generator(),
    # "05f94fe36b66db7c2164895d2b1dc5668fa35696cd6add7bf3"
    # ),
    (
     "collapse_intervals",
     collapse_intervals_generator(fixed_seed),
     "674bb82e2076379450296d830efa0337b4a3f9068a06ea0795d79662ea4f123f"
    ),
    (
     "expand_intervals",
     expand_intervals_generator(fixed_seed),
     "cc8131f1bff17c4345d3d19733479cde6a5d3f85193bed79fe"
    ),
    (
     "reverse_ascending_sublists",
     reverse_ascending_sublists_generator(fixed_seed),
     "099f999f059490e61c57e0845388f76f5dcbeda16be6aa422640750dcd4081a0"
    ),
    # Removed from problem set September 1, 2021
    # (
    # "reverse_reversed",
    # reverse_reversed_generator(fixed_seed),
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
     ryerson_letter_grade_generator(),
     "b9b86a019c4502be825b0ed52c187f9a29106a08fbbb1ffcc6"
    ),
    (
     "is_ascending",
     is_ascending_generator(fixed_seed),
     "a58079cfe1caa6768c9b9a2afb5f6ec3cf3e55526ab06578af3885213c3b8648"
    ),
    # Removed from problem set December 24, 2020
    # (
    #  "double_until_all_digits",
    #  double_until_all_digits_generator(),
    #  "7c4ba46364765cb0679f609d428bbbae8ba0df440b001c4162"
    # ),
    (
     "give_change",
     give_change_generator(fixed_seed),
     "5c38f097ab4b39598124d3983a58a10301e012ee156ac05f1a"
    ),
    (
     "winning_card",
     winning_card_generator(fixed_seed),
     "fefd8984c1559dfde64a3ecb0d3176f26e0cb4acc6ccc6f7ea"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "hand_is_badugi",
    # hand_is_badugi_generator(987),
    # "d37917aab58ce06778d3f667f6c348d1e30ee67271d9d1de60"
    # ),
    (
     "bridge_hand_shape",
     bridge_hand_generator(fixed_seed),
     "29e963cc7715f89d9a7f133e2a620702502f8eb5583d119dda6d58be58266102"
    ),
    (
     "hand_shape_distribution",
     hand_shape_distribution_generator(fixed_seed),
     "b9780dbc6fbe7a317c1e3b7a88acc599a85e5baaac692cb6cc"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "sort_by_typing_handedness",
    # sort_by_typing_handedness_generator(),
    # "919973a60cc556525aa38082a607f9981e83e5a58944d084af"
    # ),
    (
     "possible_words",
     possible_words_generator(fixed_seed),
     "20d9ac2f97454ae01d482447057d4f2b2b5c001feefd781f7e02a532a694dbfb"
    ),

    # New additions to the problem set in 2020.

    (
     "cookie",
     cookie_generator(fixed_seed),
     "e805e6415e06998231e26f5b5949ffae9f06782a5397573c8b6ff6c6358ccf61"
    ),
    (
     "eliminate_neighbours",
     eliminate_neighbours_generator(fixed_seed),
     "24333594d079471cf6696e8b660c11fc586029a178a9879c2349d154635c6aff"
    ),
    (
     "counting_series",
     counting_series_generator(fixed_seed),
     "cc67f4cef01c34c136a902ffea23a9df4e21b1991c491964bf89dc940067f569"
    ),
    # Removed from problem set December 9, 2021
    # (
    # "is_zigzag",
    # is_zigzag_generator(fixed_seed),
    # "fe5e03401a32bc5ca989759708d10a7f9d2cbd9e4821566b91"
    # ),
    # Removed from problem set October 3, 2021
    # (
    # "next_zigzag",
    # next_zigzag_generator(fixed_seed),
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
     wythoff_array_generator(fixed_seed),
     "90014bbdb273428c0f62801d34f7b225aebd9ee5ee3fdf6b002b32898e4295cd"
    ),
    (
     "hourglass_flips",
     hourglass_flips_generator(fixed_seed),
     "d80394444051437c406c3ec73bd58d15c47d7a58c20dab5351af07607fb8ac3c"
    ),
    (
     "knight_jump",
     knight_jump_generator(fixed_seed),
     "6a771380844685c2356a8a1eaf97376132aeb6f112bd6f6836"
    ),
    (
     "frog_collision_time",
     frog_collision_time_generator(fixed_seed),
     "2767a8f92c414656971210a1beeb83f20ad197d445897aff10"
    ),
    (
     "spread_the_coins",
     spread_the_coins_generator(fixed_seed),
     "5a1629f90f295d59d177cb99ea2b24e2c257f97b673ff77a67e286ae03b7279e"
    ),
    (
     "group_and_skip",
     group_and_skip_generator(fixed_seed),
     "d08b0f53bff20bc4904c534a41ca6a3c7e28519dcf9185553f3ad5e88d820bba"
    ),
    (
     "nearest_polygonal_number",
     nearest_polygonal_number_generator(fixed_seed),
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
     subtract_square_generator(fixed_seed),
     "4eedead71c2894be2e31e19bcf47a5a0786d70f6249a0274f2c2f14370b35990"
    ),
    # Removed from problem set December 9, 2021
    # (
    # "perimeter_limit_split",
    # perimeter_limit_split_generator(fixed_seed),
    # "151d96f12b67f953fae52a539f669a46b734c537ed19e3ad7b"
    # ),
    (
     "duplicate_digit_bonus",
     duplicate_digit_bonus_generator(fixed_seed),
     "7ad86f9210f78edbc645b2f9373f8f3f2cad9d2eaaa08fc088"
    ),
    # Removed from problem set September 30, 2021
    # (
    #  "count_word_dominators",
    #  count_word_dominators_generator(fixed_seed),
    #  "ade953572b3bf2540d892ae5d6c8912cd691305a494e3d009b"
    # ),
    (
     "hitting_integer_powers",
     hitting_integer_powers_generator(fixed_seed),
     "0d432b33fafce7477ca095a96d427fdddbc49fbe8e771d4f3d7ae87d51453559"
    ),
    (
     "permutation_cycles",
     permutation_cycles_generator(fixed_seed),
     "995c65239a22ee31d77c32a7269f8848b694461e5b18c8d5c1f6ea37d7d19a85"
    ),
    (
     "word_height",
     word_height_generator(fixed_seed),
     "b5454c6d98c944459ad0509a5648643feab90152f189922f36"
    ),
    (
     "mcculloch",
     mcculloch_generator(fixed_seed),
     "43549317567a9c4fdd7acaa31c7684daef2c4f3b934ed63a3f"
    ),
    (
     "trips_fill",
     trips_fill_generator(fixed_seed),
     "de71d54a6b5ef0aafca5fb50a6db63afb7a8744f434cc2f2a32cc2c274e8a037"
    ),
    (
     "is_left_handed",
     is_left_handed_generator(),
     "135b781680d9b5fbbc0815ab47ef2c0646ab7970a0b1bd0e9b"
    ),
    (
     "brussels_choice_step",
     brussels_choice_step_generator(fixed_seed),
     "30bf08918175513337d24274aa783820c4442617e8aa78969f0dcae32ae2206a"
    ),
    (
     "balanced_centrifuge",
     balanced_centrifuge_generator(fixed_seed),
     "2c81e311e4547c8f797955107aa6d2ae9d862c15ca61eaaad0cf364776bba8b8"
    ),
    (
     "lunar_multiply",
     lunar_multiply_generator(fixed_seed),
     "411dfa9dc8637871c4a257df54043301308ec7c3c09ab8ac3c"
    ),
    (
     "oware_move",
     oware_move_generator(fixed_seed),
     "7bb8b1b98cc604baf4e71970520efacca01698de168f20628dda2aa48dd8ea5e"
    ),
    (
     "conjugate_regular",
     conjugate_regular_generator(),
     "132c4df527db578df034041f0cfd63eda6c98f452b9d8eb460"
    ),

    # New additions to the problem set in 2021.

    (
     "reach_corner",
     reach_corner_generator(fixed_seed),
     "0255ef6a81a2989825f1070f5b44ab9c0ccadcb796e34bffd0"
    ),
    (
     "bulgarian_cycle",
     bulgarian_cycle_generator(fixed_seed),
     "59be2b964195790855c6028c7296c9c894e90420677d3f065a"
    ),
    (
     "prominences",
     prominences_generator(fixed_seed),
     "e762bc4e666e335d700dea39e375b87c9827f4593e504e2dec783f13a33884da"
    ),
    (
     "leibniz",
     leibniz_generator(fixed_seed),
     "ef3258160b68e07f3b5af2d6560d68221be321c040293d4c5493f1e6ee7e8a48"
    ),
    (
     "candy_share",
     candy_share_generator(fixed_seed),
     "5c83954002c783e3e283cf6d9a0b8500e179f15ba6a31eb4be4db1258daa4230"
    ),
    (
     "reverse_110",
     reverse_110_generator(fixed_seed),
     "52883da9877e7796e9f62f496e17de82e4b787bcda34da9d2b"
    ),
    (
     "colour_trio",
     colour_trio_generator(fixed_seed),
     "0b9f0e3ce49d5eea0073721da2ee28654151a1e2653f9b64745b65e07bf25780"
    ),
    (
     "wordomino",
     wordomino_generator(),
     "5b081cc381ec8ddaa382d8450def04b53255ee62b67356f690"
    ),
    # Removed from problem set April 18, 2022
    # (
    # "recaman_item",
    # recaman_item_generator(),
    # "e36c779db6a77037f4e0c11363e4377a1dfe773cb0c7af8617"
    # ),
    (
     "count_troikas",
     count_troikas_generator(fixed_seed),
     "9d593bfe53a18d6a6e8e355a27fa5c82efb999cf2198e60e79"
    ),
    (
     "count_corners",
     count_corners_generator(fixed_seed),
     "d48250dd2102d522025cc1f7ae8db9ea645c274eb366ab0c64"
    ),
    (
     "cut_corners",
     count_corners_generator(fixed_seed, 1500),
     "19cf15c0b8970c57145f2fdc4c4cad646a30d56c74c53857145310e2dddf6010"
    ),
    (
     "domino_tile",
     domino_tile_generator(fixed_seed),
     "d995b963593be92f0e3068ae9f2286159b24d03a49efb416a8c288c95c93c6c2"
    ),
    (
     "collect_numbers",
     collect_numbers_generator(fixed_seed),
     "99afb2b51423f6223f4b51c09914f81cf6a6d12ad536e8b08bf51309c80ca798"
    ),
    (
     "cut_into_squares",
     cut_into_squares_generator(fixed_seed),
     "fb698d6bcd2422488b6ab1acb491740e4a56f0c20e61f6ccd4f69d65f0371529"
    ),

    # New additions to the problem set in 2022.

    (
     "laser_aliens",
     laser_aliens_generator(fixed_seed),
     "64186671716042ed9238ea75d0104cbb932a0e37e0275303f83d953a95534693"
    ),
    (
     "stepping_stones",
     stepping_stones_generator(fixed_seed),
     "c4ac30082fa34bc0f947fc1ddf3964c92dce0acac4e7a945dec84237124d28a4"
    ),
    (
     "verify_betweenness",
     verify_betweenness_generator(fixed_seed),
     "16b9176a15ffd0a8da7cbd5a125627fa68b6eca4ad01523515b95b0c8092f342"
    ),
    (
     "illuminate_all",
     illuminate_all_generator(fixed_seed),
     "2b21126bfe7cc7abbfd45d6a9da7d2899a7db69bce0ffac0958d33fce3dcc7e1"
    ),
    (
     "best_clubs",
     best_clubs_generator(fixed_seed),
     "cf82279e4ea8b4e1bd79d62c00243a210076bfb3d59dff4b0516520ff77e02f4"
    ),
    (
     "both_ways",
     both_ways_generator(fixed_seed),
     "9bfb5ef40a0c6347cd8594aa443a10462194792cd36089acae5a00071bbeb534"
    ),
    (
     "staircase",
     staircase_generator(fixed_seed),
     "20ceca8a5fea22f23dfba0b567555aeb5a8dc4553f03bf34b7fbb121de9d5f9e"
    ),
    (
     "ordinal_transform",
     ordinal_transform_generator(fixed_seed),
     "de7f04aa8f6ea61b43a89bf9cce0dc594f856d7fdc7963ba12273dc09eb47568"
    )
]


def run_all():
    print(f"109 Python Problems tester, {version}, Ilkka Kokkarinen.")
    try:
        if version_info < (3, 7, 0):
            print("THIS SCRIPT REQUIRES PYTHON 3.7.0 OR LATER. EXITING.")
            exit(1)
        implemented = sort_by_source(testcases)
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
                if not verified:
                    print(f"YOU ARE USING A VERY OBSOLETE VERSION OF {expected_answers_file}. EXITING.")
                    exit(3)
                else:
                    print(f"Finished reading expected answers.")
                    test_all_functions(labs109, testcases, known=known)
            else:
                # If the record file doesn't exist, record the model answers.
                with gzip.open(expected_answers_file, 'wt') as rf:
                    test_all_functions(labs109, testcases, recorder=rf)
        else:
            print("Testing functions without using recorded expected answers.")
            test_all_functions(labs109, testcases, known=None)
    except Exception as e:
        print(f"TESTER CRASHED WITH ERROR: {e}")
        exit(4)


run_all()
