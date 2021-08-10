# Automated tester for the problems in the collection
# "109 Python Problems for CCPS 109" by Ilkka Kokkarinen.
# Ilkka Kokkarinen, ilkka.kokkarinen@gmail.com

# Requires Python 3.7+ and the guarantee to iterate collections
# in the insertion order to run all test cases correctly.

# For instructors who want to add their own problems to this set:
#
# 1. Set the value of use_record to False.
# 2. Write your private solution function to top of your private
#    model solutions file labs109.py.
# 3. Write your test case generator in this script below.
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

from hashlib import sha256
from time import time
from itertools import islice
import random
import gzip
import os.path
from sys import version_info, exit
import labs109

# The release date of this version of the CCPS 109 tester.
version = "August 9, 2021"

# Fixed seed used to generate pseudorandom numbers.
fixed_seed = 12345

# How many test cases to record in the file for each function.
testcase_cutoff = 300

# Name of the file that contains the expected answers.
recordfile = 'expected_answers'

# Whether to use the expected correct answers when they exist.
use_record = True

# Markers used to separate the parts of the expected answers file.
# These should never appear as the prefix of any expected answer.
version_prefix = '<$$$$>'
function_prefix = '<****>'

# Timeout until the test for a function is terminated as too slow.
timeout_cutoff = 20

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


# When reporting an error, try not to flood the user console.

def emit_args(args, cutoff=100):
    for (i, a) in enumerate(args):
        if i > 0:
            print(", ", end='')
        if type(a) == list or type(a) == tuple:
            if len(a) < cutoff:
                print(a, end='')
            else:
                left = ", ".join([str(x) for x in a[:5]])
                right = ", ".join([str(x) for x in a[-5:]])
                print(f"[{left}, <{len(a)-10} omitted...>, {right}]", end='')
        else:
            print(repr(a) if len(repr(a)) < 100 else '[...]', end='')
    print()


# Given teacher and student implementations of the same function, run
# the test cases for both of them and output the first or the shortest
# test case for which these two implementations disagree.

def discrepancy(teacher, student, test_cases, stop_at_first=False):
    shortest, d1, d2, disc, cases = None, None, None, 0, 0
    for n, elem in enumerate(test_cases):
        elem2 = elem[:]  # In case student function messes up elem...
        cases += 1
        try:
            r1 = canonize(teacher(*elem))
        except Exception as e:
            r1 = f"TEACHER CRASH! {e}"
        try:
            r2 = canonize(student(*elem))
        except Exception as e:
            r2 = f"STUDENT CRASH! {e}"
        if r1 != r2:
            disc += 1
            if (stop_at_first or shortest is None or
                    len(str(elem2)) < len(shortest)):
                shortest, d1, d2 = elem2, r1, r2
            if stop_at_first:
                break
    if shortest is None:
        print("Both functions returned the same answers.")
        return True
    else:
        if stop_at_first:
            print("First discrepancy found.")
        else:
            print(f"For {cases} test cases, found {disc} discrepancies.")
            print("Shortest discrepancy input was:")
        emit_args(shortest)
        print(f"Teacher: {repr(d1)}")
        print(f"Student: {repr(d2)}")
        return False


# Runs the function f for its test cases, calculating SHA256 checksum
# of the results. If the checksum matches the expected, return the
# running time, otherwise return -1. If expected == None, print out
# the computed checksum instead. If recorder != None, print out the
# arguments and expected result into the recorder.

def test_one_function(f, test_cases, expected=None, recorder=None, known=None):
    fname, recorded = f.__name__, None
    print(f"{fname}: ", end="", flush=True)
    if recorder:
        print(f"{function_prefix}{fname}", file=recorder)
    if known:
        recorded = known.get(fname, None)
    chk, start_time, crashed = sha256(), time(), False
    for (count, test) in enumerate(test_cases):
        if not isinstance(test, tuple):
            test = (test,)
        try:
            result = f(*test)
        except Exception as e:  # catch any exception
            crashed = True
            print(f"CRASH AT TEST CASE #{count}: {e}")
            break
        # If the result is a set or dictionary, turn it into sorted list first.
        result = canonize(result)
        # Update the checksum.
        sr = str(result)
        chk.update(sr.encode('utf-8'))
        if recorder:
            print(sr.strip()[:300], file=recorder)
            if count >= testcase_cutoff:
                break
        if use_record and known and count < testcase_cutoff and recorded:
            should_be = recorded[count]
            if len(should_be) < 295:
                ok = sr.strip() == should_be
            else:
                ok = sr.strip().startswith(should_be)
            if not ok:
                crashed = True
                print(f"DISCREPANCY AT TEST CASE #{count}: ")
                print("ARGUMENTS: ", end="")
                emit_args(test)
                trail = '...' if len(should_be) == 300 else ''
                print(f"EXPECTED: {should_be} {trail}")
                print(f"RETURNED: {sr}")
                break
        total_time = time() - start_time
        if total_time > timeout_cutoff:
            print(f"TIMEOUT AT TEST CASE #{count}. REJECTED AS TOO SLOW.")
            crashed = True
            break
    if not recorder:
        total_time = time() - start_time
        digest = chk.hexdigest()
        if not crashed and not expected:
            print(digest[:50])  # Expected checksum for the instructor
            return total_time
        elif not crashed and digest[:len(expected)] == expected:
            print(f"Success in {total_time:.3f} seconds.")
            return total_time
        elif crashed:
            return -1
        else:
            print("CHECKSUM MISMATCH: AT LEAST ONE RETURNED ANSWER WAS WRONG.")
            return -1
    else:
        return 0


# Sort the suite of test cases according to the order in which
# they appear in the student source code.

def sort_by_source(suite):
    funcs = dict()
    with open('labs109.py', 'r', encoding='utf-8') as source:
        for (lineno, line) in enumerate(source):
            if line.startswith("def "):
                fname = line[4:line.find('(')].strip()
                if fname in funcs:
                    print(f"Warning: multiple definition for {fname}")
                funcs[fname] = lineno
        suite.sort(key=lambda x: funcs.get(x[0], 9999999))
    return suite


# Runs the tests for all functions in the suite, returning the
# count of how many of those were implemented and passed the test.

def test_all_functions(module, suite, recorder=None, known=None):
    if recorder:
        print("RECORDING THE RESULTS OF INSTRUCTOR MODEL SOLUTIONS.")
        print("IF YOU ARE A STUDENT, YOU SHOULD NOT BE SEEING THIS")
        print(f"MESSAGE!!! ENSURE THAT THE FILE {recordfile} FROM")
        print("WHEREVER YOU DOWNLOADED THIS AUTOMATED TESTER IS ALSO")
        print("IN THIS SAME WORKING DIRECTORY!!!")
        print()
    count, total = 0, 0
    if recorder:
        print(f"{version_prefix}{version}", file=recorder)
    for (fname, test_cases, expected) in sort_by_source(suite):
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
        print(f"of {len(suite)} possible work.")
    return count


ups = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
lows = "abcdefghijklmnopqrstuvwxyz"


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


# Produce a random n-digit integer with repeating digits.

def random_int(rng, n, prob=70):
    r, curr = 0, rng.randint(1, 9)
    for _ in range(n):
        r = 10 * r + curr
        if rng.randint(0, 99) < prob:
            curr = rng.randint(0, 9)
    return r


# This function replaced warandpeace.txt as the source of text data.
# Since none of the problems using that file were linguistic, it
# was pointless to use real text to test them, helping us shed
# a few megs of dead weight from this project folder.

def random_text_generator(seed, n=70):
    rng = random.Random(seed)
    alpha = lows
    alpha += alpha.upper()
    punct = '.,!?'
    for _ in range(10000):
        line = ""
        while len(line) < n:
            word = "".join([rng.choice(alpha) for _ in range(rng.randint(1, 20))])
            line += " " if len(line) > 0 else ""
            line += word
            if rng.randint(0, 99) < 20:
                line += rng.choice(punct)
        yield line


# Create a random n-character string from the given alphabet.

def random_string(alphabet, n, rng):
    result = ''
    for _ in range(n):
        result += rng.choice(alphabet)
    return result


# The test case generators for the individual functions.

def brussels_choice_step_generator(seed):
    rng = random.Random(seed)
    for (i, n) in enumerate(islice(scale_random(seed, 2, 10), 2000)):
        n += 10
        nn = len(str(n))
        a = rng.randint(1, nn)
        b = rng.randint(1, nn)
        yield n, min(a, b), max(a, b)


def ryerson_letter_grade_generator():
    for i in range(0, 150):
        yield i


def is_ascending_generator(seed):
    yield [1, 2, 2]    # Because students don't read instructions
    rng = random.Random(seed)
    for i in range(500):
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
    # Start with some small cases to aid first debugging
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
    for i in range(3000):
        n = rng.randint(2, 3 + i // 50)
        pn = rng.randint(0, n + 2)
        pieces = set()
        while len(pieces) < pn:
            px = rng.randint(0, n - 1)
            py = rng.randint(0, n - 1)
            if (px, py) not in pieces:
                pieces.add((px, py))
        yield n, list(pieces)


def rooks_with_friends_generator(seed):
    rng = random.Random(seed)
    for (n, pieces) in safe_squares_generator(seed):
        fn = rng.randint(0, n)
        yield n, pieces[:fn], pieces[fn:]
        yield n, pieces[fn:], pieces[:fn]


def double_until_all_digits_generator():
    for i in range(3000):
        yield i


def first_preceded_by_smaller_generator(seed):
    rng = random.Random(seed)
    count, goal = 0, 1
    items = []
    for i in range(20000):
        items.append(rng.randint(-3 - i, 3 + i))
        if len(items) > 3:
            j = rng.randint(0, len(items) - 1)
            items[-1], items[j] = items[j], items[-1]
        yield items[:], rng.randint(1, 2 + len(items) // 2)
        count += 1
        if count == goal:
            count, goal = 0, goal + 2
            items = [rng.randint(-3 - i, 3 + i) for _ in range(1 + i // 100)]


def maximum_difference_sublist_generator(seed):
    rng = random.Random(seed)
    for i in range(1000):
        len_ = rng.randint(1, 100)
        items = [rng.randint(0, 10000) for _ in range(len_)]
        for k in range(1, len_ + 1):
            yield items[:], k


def count_and_say_generator(seed):
    rng = random.Random(seed)
    for i in range(3000):
        bursts = rng.randint(1, 4 + i // 10)
        digits = ''
        for j in range(bursts):
            n = rng.randint(1, min(20, j + 4))
            digits += rng.choice('0123456789') * n
        yield digits


def group_equal_generator(seed):
    rng = random.Random(seed)
    for i in range(50):
        for j in range(10):
            items = []
            bursts = rng.randint(1, 2 + i // 5)
            for k in range(bursts):
                n = rng.randint(1, 2 + i // 5)
                v = rng.randint(0, 10 + i // 20)
                items.extend([v] * n)
            yield items,


def longest_palindrome_generator(seed):
    rng = random.Random(seed)
    for i in range(1000):
        p1 = rng.randint(0, i + 3)
        p2 = rng.randint(2, i + 3)
        p3 = rng.randint(0, i + 3)
        left = random_string(lows, p1, rng)
        middle = random_string(lows, p2, rng)
        if rng.randint(0, 1) == 1:
            middle += middle[::-1]
        else:
            middle += middle[:len(middle)-1:-1]
        right = random_string(lows, p3, rng)
        yield left + middle + right


def reverse_ascending_sublists_generator(seed):
    rng = random.Random(seed)
    for i in range(1000):
        for _ in range(5):
            yield [rng.randint(0, 2*i + k) for k in range(i + 1)]


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


def hand_is_badugi_generator(seed):
    rng = random.Random(seed)
    for _ in range(100000):
        yield rng.sample(deck, 4)


def bridge_hand_shape_generator(seed):
    rng = random.Random(seed)
    for _ in range(20000):
        yield rng.sample(deck, 13)


def winning_card_generator(seed):
    rng = random.Random(seed)
    for _ in range(10000):
        hand = rng.sample(deck, 4)
        for trump in suits:
            yield hand[:], trump
        yield hand[:], None


def hand_shape_distribution_generator(seed):
    rng = random.Random(seed)
    for i in range(2, 71):
        hands = [rng.sample(deck, 13) for _ in range(i * i)]
        yield hands


def milton_work_point_count_generator(seed):
    rng = random.Random(seed)
    for _ in range(10000):
        hand = rng.sample(deck, 13)
        for suit in suits:
            yield hand, suit
        yield hand, 'notrump'


def sort_by_typing_handedness_generator():
    f = open('words_sorted.txt', 'r', encoding='utf-8')
    words = [x.strip() for x in f]
    f.close()
    yield words


def possible_words_generator(seed):
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    rng = random.Random(seed)
    for n in range(40):
        patword = rng.choice(words)
        letters = sorted(list(set(c for c in patword)))
        if len(letters) > 3:
            k = len(letters) - rng.randint(1, len(letters) - 3)
            guessed = rng.sample(letters, k)
            pat = ''
            for ch in patword:
                pat += ch if ch in guessed else '*'
            yield words, pat


def postfix_evaluate_generator(seed):
    rng = random.Random(seed)
    for _ in range(1000):
        exp = []
        count = 0
        while len(exp) < 5 or count != 1:
            if count > 1 and (count > 10 or rng.randint(0, 99) < 50):
                exp.append(rng.choice(['+', '-', '*', '/']))
                count -= 1
            else:
                exp.append(rng.randint(1, 10))
                count += 1
        yield exp


def __create_list(d, rng):
    if d < 1:
        return rng.randint(1, 100)
    else:
        n = rng.randint(0, 2 + d)
        return [__create_list(d - rng.randint(1, 3), rng) for _ in range(n)]


def reverse_reversed_generator(seed):
    rng = random.Random(seed)
    n = 3
    for i in range(300):
        yield __create_list(3 + n, rng)
        if i % 50 == 49:
            n += 1


def scrabble_value_generator(seed):
    rng = random.Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    for word in words:
        multipliers = [rng.randint(1, 3) for _ in range(len(word))]
        yield word, multipliers if rng.randint(0, 99) < 50 else None


def expand_intervals_generator(seed):
    yield ''
    rng = random.Random(seed)
    for j in range(2000):
        curr = 0
        result = ''
        first = True
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
    yield []
    rng = random.Random(seed)
    for i in range(1000):
        items, curr = [], 1
        n = rng.randint(1 + i // 2, i + 3)
        for j in range(n):
            m = rng.randint(1, 4 + i // 50)
            for k in range(m):
                items.append(curr)
                curr += 1
            curr += rng.randint(2, 10 + i * i)
        yield items


def recaman_generator():
    for n in range(1, 6):
        yield 10**n


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
                cows = min(cows, 4 - bulls)
                if not(bulls == 3 and cows == 1):
                    result.append((guess, bulls, cows))
        yield result


def contains_bingo_generator(seed):
    rng = random.Random(seed)
    nums = range(1, 99)
    for _ in range(10000):
        card = rng.sample(nums, 25)
        card = [card[i:i+5] for i in range(0, 25, 5)]
        m = rng.randint(20, 80)
        numbers = rng.sample(nums, m)
        numbers.sort()
        centerfree = [True, False][rng.randint(0, 1)]
        yield card, numbers, centerfree


def can_balance_generator(seed):
    rng = random.Random(seed)
    for i in range(500):
        for j in range(10):
            left, lm = [], 0
            right = [rng.randint(1, i + 2)]
            rm = right[0]
            while lm != rm and lm + rm < 20 * (i+3):
                v = rng.randint(1, i + 5)
                s = rng.randint(0, 1)
                if len(left) + len(right) > i + j + 3:
                    if lm < rm:
                        s, v = 0, (rm - lm) // (len(left) + 1)
                    else:
                        s, v = 1, (lm - rm) // (len(right) + 1)
                v = max(v, 1)
                if s == 0:
                    left.append(v)
                    lm += v * len(left)
                else:
                    right.append(v)
                    rm += v * len(right)
            yield left[::-1] + [rng.randint(1, i+2)] + right


def calkin_wilf_generator():
    for v in [10, 42, 255, 987, 7654, 12356]:
        yield v


def fibonacci_sum_generator(seed):
    for v in islice(scale_random(seed, 2, 4), 1500):
        yield v


def create_zigzag_generator(seed):
    rng = random.Random(seed)
    for i in range(10000):
        rows = rng.randint(1, 1 + i // 100)
        cols = rng.randint(1, 1 + i // 100)
        start = rng.randint(1, 100 + i)
        yield rows, cols, start


def fibonacci_word_generator(seed):
    for v in islice(scale_random(seed, 3, 6), 2000):
        yield v


def all_cyclic_shifts_generator():
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    yield from words


def aliquot_sequence_generator():
    for i in range(1, 130):
        yield i, 10
        yield i, 100


def josephus_generator(seed):
    rng = random.Random(seed)
    hop, skip = 1, 1
    for n in range(2, 100):
        for k in range(1, n):
            if n > 20 and rng.randint(0, 99) < 5:
                yield hop, skip + rng.randint(2, 10) ** n
            else:
                yield hop, skip
            skip += rng.randint(1, 2 + k)
        hop += rng.randint(1, 3 + n // 20)


def balanced_ternary_generator(seed):
    yield 0    # Important edge case
    for v in islice(scale_random(seed, 3, 10), 2000):
        yield v
        yield -v


__names = ["brad", "ben", "britain", "donald", "bill", "ronald",
           "george", "laura", "barbara", "barack", "angelina",
           "jennifer", "ross", "rachel", "monica", "phoebe",
           "joey", "chandler", "hillary", "michelle", "melania",
           "nancy", "homer", "marge", "bart", "lisa", "maggie",
           "waylon", "montgomery", "california", "canada",
           "germany", "sheldon", "leonard", "rajesh", "howard",
           "penny", "amy", "bernadette", "oumoumou"]


def brangelina_generator(seed):
    rng = random.Random(seed)
    for _ in range(20000):
        first = rng.choice(__names)
        second = rng.choice(__names)
        yield first, second
        yield second, first


def frequency_sort_generator(seed):
    rng = random.Random(seed)
    count, goal = 0, 1
    items = []
    for i in range(10000):
        yield items[:]
        count += 1
        if count == goal:
            count, goal = 0, goal + 2
            items = []
        else:
            if len(items) < 3 or rng.randint(0, 99) < 30:
                items.append(rng.randint(-3 - i*i*i, 3 + i*i*i))
            items.append(rng.choice(items))


def count_consecutive_summers_generator():
    for i in range(1, 1000):
        yield i


def detab_generator(seed):
    rng = random.Random(seed)
    for (line,) in random_text_generator(seed):
        line = line.replace(' ', '\t')
        n = rng.randint(1, 7)
        yield line, n, ' '


def iterated_remove_pairs_generator(seed):
    rng = random.Random(seed)
    for k in range(1000):
        n = rng.randint(0, 100)
        vals = [rng.randint(1, 10000) for _ in range(7)]
        yield [vals[rng.randint(0, 6)] for _ in range(n)],


def is_perfect_power_generator(seed):
    rng = random.Random(seed)
    for k in range(300):
        base = rng.randint(2, 3 + k // 4)
        exp = rng.randint(2, 3 + k // 10)
        off = rng.randint(-1, +1)
        yield base ** exp - off,


def sort_by_digit_count_generator(seed):
    yield [],
    yield [42],
    rng = random.Random(seed)
    count, goal, n = 0, 1, 1
    for k in range(10000):
        yield [rng.randint(1, 5 + n * n * n * n) for _ in range(n)],
        count += 1
        if count > goal:
            count, goal, n = 0, goal + 10, n + 1


def count_divisibles_in_range_generator(seed):
    prev = 0
    vals = islice(scale_random(seed, 2, 6), 1000)
    divs = islice(scale_random(seed, 2, 20), 1000)
    for (v, k) in zip(vals, divs):
        yield prev, v, k
        yield -prev, v, k
        prev = v


__players = ['anita', 'suzanne', 'suzy', 'tom', 'steve',
             'ilkka', 'rajesh', 'amy', 'penny', 'sheldon',
             'leonard', 'bernadette', 'howard']


def highest_n_scores_generator(seed):
    rng = random.Random(seed)
    for _ in range(10000):
        scores = [(name, rng.randint(1, 100)) for name in __players for _ in range(rng.randint(0, 20))]
        n = rng.randint(1, 10)
        yield scores, n


def bridge_hand_shorthand_generator(seed):
    rng = random.Random(seed)
    for _ in range(10000):
        yield rng.sample(deck, 13)


def losing_trick_count_generator(seed):
    rng = random.Random(seed)
    for _ in range(10000):
        yield rng.sample(deck, 13)


def prime_factors_generator(seed):
    for v in islice(scale_random(seed, 2, 30), 500):
        yield v


def factoring_factorial_generator(seed):
    for v in islice(scale_random(seed, 2, 10), 100):
        yield v


def riffle_generator(seed):
    rng = random.Random(seed)
    for i in range(1000):
        items = [rng.randint(-i*i, i*i) for _ in range(2 * i)]
        yield items[:], True
        yield items, False


def words_with_given_shape_generator(seed):
    rng = random.Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    for _ in range(30):
        pattern = [rng.randint(-1, 1) for _ in range(rng.randint(5, 10))]
        yield words, pattern


def squares_intersect_generator(seed):
    rng = random.Random(seed)
    for i in range(100000):
        r = 5 + i // 100
        x1 = rng.randint(-r, r)
        y1 = rng.randint(-r, r)
        d1 = rng.randint(-r, r)
        x2 = rng.randint(-r, r)
        y2 = rng.randint(-r, r)
        d2 = rng.randint(-r, r)
        b = rng.randint(2, 11)
        s = b ** rng.randint(1, 2 + i // 10000)
        yield (s * x1, s * y1, s * d1), (s * x2, s * y2, s * d2)


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


def pancake_scramble_generator(seed):
    rng = random.Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    for _ in range(10000):
        yield rng.choice(words)


def lattice_paths_generator(seed):
    rng = random.Random(seed)
    for i in range(1000):
        x = rng.randint(2, 3 + i // 40)
        y = rng.randint(2, 3 + i // 40)
        tabu = set()
        n = rng.randint(1, max(1, x*y // 10))
        while len(tabu) < n:
            xx = rng.randint(0, x)
            yy = rng.randint(0, y)
            tabu.add((xx, yy))
        yield x, y, list(tabu)


def count_carries_generator(seed):
    rng = random.Random(seed)
    n, count, goal = 1, 0, 2
    for _ in range(20000):
        a = random_int(rng, n + rng.randint(0, 5), 70)
        b = random_int(rng, n + rng.randint(0, 5), 50)
        yield a, b
        yield a, a
        yield b, a
        count += 1
        if count == goal:
            n, count, goal = n + 1, 0, goal * 2


def count_squares_generator(seed):
    rng = random.Random(seed)
    for i in range(1000):
        pts = set()
        w = rng.randint(3, 4 + i // 50)
        h = rng.randint(3, 4 + i // 50)
        n = rng.randint(1, (w * h) // 3)
        while len(pts) < n:
            x = rng.randint(0, w)
            y = rng.randint(0, h)
            pts.add((x, y))
        yield list(pts)


def kempner_generator():
    for i in range(1, 1000, 10):
        yield i


def tribonacci_generator():
    for i in range(1000):
        yield i, (1, 1, 1)
        yield i, (1, 0, 1)
        yield i, (1, 2, 3)


def is_permutation_generator(seed):
    rng = random.Random(seed)
    for n in range(1, 1000):
        items = rng.sample(list(range(1, n+1)), n)
        yield items[:], n
        m = rng.randint(1, 5)
        for _ in range(m):
            j = rng.randint(0, n - 1)
            v = items[j]
            if rng.randint(0, 99) < 50:
                k = rng.randint(0, n - 1)
                items[j] = items[k]
            else:
                items[j] = n + 1
            yield items[:], n
            items[j] = v


def three_summers_generator(seed):
    rng = random.Random(seed)
    count, goal = 0, 1
    items = []
    for i in range(400):
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


def first_missing_positive_generator(seed):
    rng = random.Random(seed)
    for i in range(1000):
        n = rng.randint(10, 1000)
        items = [rng.randint(1, 2*n) for _ in range(n)]
        rng.shuffle(items)
        yield items


def ztalloc_generator(seed):
    yield from ['d', 'uuddd', 'ddd', 'udud', 'uduuudddd']
    rng = random.Random(seed)
    for i in range(50000):
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


def count_distinct_sums_and_products_generator(seed):
    rng = random.Random(seed)
    for n in range(200):
        items = [rng.randint(1, 10)]
        for i in range(n):
            items.append(items[-1] + rng.randint(1, 10))
        yield items


def seven_zero_generator():
    for n in range(2, 501):
        yield n


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
        yield items[:], rng.randint(1, 2 + i // 100)
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

    for word in ["entiyt", "mopp", "laval", "hellx", "sassage", "bumpxious",
                 "sapeebe", "skekeron", "possobilities", "arvanat", "mossberg",
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
    for i in range(1000):
        d = rng.randint(1, i + 3)
        m = d // 2
        n = 0
        for j in range(d):
            n = 10 * n
            if j == m:
                if rng.randint(0, 99) < 20:
                    n += rng.randint(1, 9)
            elif rng.randint(0, 99) < 99:
                n += rng.randint(1, 9)
        yield n


def words_with_letters_generator():
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    for letters in ["smoom", "reflux", "yoam", "xxx", "abba", "ubu", "rentob", "whoa"]:
        yield words, letters


def extract_increasing_generator(seed):
    rng = random.Random(seed)
    for i in range(1000):
        n = rng.randint(i, i + 10)
        digits = "".join([rng.choice('0123456789') for _ in range(n)])
        yield digits


def square_follows_generator(seed):
    def emit():
        rng = random.Random(seed)
        curr = 1
        step = 3
        for _ in range(10**6):
            yield curr
            curr += rng.randint(2, step)
            step += 1
    yield emit()


def line_with_most_points_generator(seed):
    yield [(3, 0), (4, 4), (3, 3), (3, -1)]
    yield [(5, 5), (7, 7), (1, 5), (42, 5), (42, 7), (42, 42), (-4, 5)]
    rng = random.Random(seed)
    pts = set()
    count, goal = 0, 1
    for i in range(150):
        count += 1
        if count == goal:
            count, goal = 0, goal + 1
            pts = set()
        sx = rng.randint(-3-i, 3+i)
        sy = rng.randint(-3-i, 3+i)
        dx = 0 if rng.randint(0, 99) < 30 else rng.randint(-10, 10)
        dy = 0 if dx != 0 and rng.randint(0, 99) < 30 else rng.randint(-10, 10)
        for j in range(count + 1):
            pts.add((sx + dx * j, sy + dy * j))
        pts_list = list(pts)
        yield pts_list


def count_maximal_layers_generator(seed):
    rng = random.Random(seed)
    for i in range(300):
        n = 3 + i
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
    poss = ['cat', 'tac', 'dog', 'god']
    animals = []
    goal, count = 5, 0
    for _ in range(5000):
        count += 1
        if count == goal:
            count, goal = 0, goal + 2
            animals = []
        animals.append(rng.choice(poss))
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


def bridge_score_generator():
    for suit in ['clubs', 'hearts', 'spades', 'notrump']:
        for level in range(1, 8):
            for vul in [False, True]:
                for dbl in ['', 'X', 'XX']:
                    for made in range(level, 8):
                        yield suit, level, vul, dbl, made


def max_checkers_capture_generator(seed):
    rng = random.Random(seed)
    for i in range(300):
        n = 6 + i // 50
        pieces = set()
        for j in range(1, n):
            while len(pieces) < 3 * j:
                px = rng.randint(0, n - 1)
                py = rng.randint(0, n - 1)
                if py % 2 != px % 2:
                    py += -1 if py > 0 else +1
                pieces.add((px, py))
            count = 0
            while count < 2 * n:
                x = rng.randint(0, n - 1)
                y = rng.randint(0, n - 1)
                if y % 2 != x % 2:
                    y += -1 if y > 0 else +1
                if (x, y) not in pieces:
                    count += 1
                    yield n, x, y, set(pieces)


def collatzy_distance_generator(seed):
    rng = random.Random(seed)
    for a in range(200):
        b = rng.randint(1, a + 5)
        yield a, b
        yield b, a


def nearest_smaller_generator(seed):
    rng = random.Random(seed)
    count, goal, scale = 0, 1, 1
    items = []
    for i in range(4000):
        r = 3 + i * i * scale
        count += 1
        if count == goal:
            count, goal = 0, goal + 2
            scale += 2
            items = [rng.randint(-r, r) for _ in range(1 + i // 10)]
        items.append(rng.randint(-r, r))
        j = rng.randint(0, len(items) - 1)
        items[j], items[-1] = items[-1], items[j]
        if rng.randint(0, 99) < 20:
            items[rng.randint(0, len(items) - 1)] = items[-1]
        yield items[:]


def double_trouble_generator(seed):
    items = ['joe', 'bob', 42, 99]
    rng = random.Random(seed)
    curr, step = 1, 1
    for _ in range(200):
        yield items[:], curr
        curr += rng.randint(1, step)
        step = step * 2
        items.append(items[-1] + 1)


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


def van_eck_generator():
    curr = 1
    for _ in range(23):
        yield curr
        curr = 2 * curr


def suppressed_digit_sum_generator(seed):
    rng = random.Random(seed)
    curr = 1
    for _ in range(500):
        yield curr
        curr = 10 * curr + rng.randint(0, 9)


def unscramble_generator(seed):
    rng = random.Random(seed)
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    count = 0
    while count < 500:
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
    for _ in range(100):
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


def forbidden_substrings_generator():
    yield 'ABCDE', 5, ['A', 'B', 'C', 'D']
    yield 'ABCD', 3, ['AA', 'BB', 'CC']
    yield 'FG', 4, ['FGG', 'GFF', 'FFF']
    yield 'PQR', 2, ['PP', 'QR']
    yield 'XABCD', 2, []
    yield 'REB', 6, ['RR', 'EE', 'BE', 'BRR']
    yield 'MOS', 5, ['SO', 'SM', 'SS']
    yield 'ABC', 9, ['AB', 'BBB', 'AAAA', 'CC', 'ACAC', 'CBA', 'CA', 'BAC']
    yield 'XYZ', 5, ['XY', 'YZ', 'ZX']
    yield 'ABCDEFG', 100, ['B', 'C', 'D', 'E', 'F', 'G']
    yield 'MOA', 7, ['MOA', 'AOM', 'AMO', 'MAO']
    yield 'ARB', 9, ['ABB', 'RRR', 'RAB', 'RARB']


def count_dominators_generator(seed):
    rng = random.Random(seed)
    items = []
    count, goal = 0, 10
    for _ in range(100000):
        yield items[:]
        count += 1
        if count == goal:
            count, goal = 0, goal + 2
            items = []
        r = (goal - count)**3
        items.append(rng.randint(-r, r))


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


def count_distinct_lines_generator(seed):
    rng = random.Random(seed)
    for i in range(100):
        n = 3 + i
        points = set()
        for j in range(n):
            x = rng.randint(1, n*n)
            y = rng.randint(1, n*n)
            points.add((x, y))
        yield list(points)


def bulgarian_solitaire_generator(seed):
    rng = random.Random(seed)
    for k in range(2, 30):
        for i in range(2 + 5 * k):
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
    for i in range(1000):
        towers = []
        w = i * i + 5
        max_area = w * w // 10
        for k in range(3 + i // 10):
            s = rng.randint(1, w)
            e = s + rng.randint(1, 3 * i + 1)
            max_height = 1 + max_area // (e - s)
            h = rng.randint(1, max_height)
            towers.append((s * scale, e * scale, h * scale))
        yield towers
        if i % 100 == 0:
            scale *= rng.randint(3, 6)


def fractran_generator(seed):
    rng = random.Random(seed)
    conway = [(17, 91), (78, 85), (19, 51), (23, 38), (29, 33),
              (77, 29), (95, 23), (77, 19), (1, 17), (11, 13),
              (13, 11), (15, 2), (1, 7), (55, 1)]
    for n in range(2, 100):
        yield n, conway[:], 100
    for i in range(10):
        for j in range(10):
            prog = []
            for k in range(2, i + j):
                num = rng.randint(1, 100)
                den = rng.randint(1, 100)
                prog.append((num, den))
            n = rng.randint(2, 10)
            yield n, prog, 30


def scylla_or_charybdis_generator(seed):
    rng = random.Random(seed)
    for n in range(2, 40):
        for i in range(2 * n):
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


def fractional_fit_generator(seed):
    rng = random.Random(seed+1)
    for n in range(3, 12):
        for _ in range(n*n):
            fs = []
            for _ in range(n + 1):
                a = rng.randint(0, n*n)
                b = rng.randint(a + 1, n*n + 3)
                fs.append((a, b))
            yield fs


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


def sublist_with_mostest_generator(seed):
    rng = random.Random(seed)
    for n in range(11, 80):
        items, step = [rng.randint(1, 10)], 2
        for j in range(n):
            items.append(items[-1] + rng.randint(1, step))
            if j % 5 == 0:
                step += rng.randint(1, 5)
        for k in range(9, n // 2):
            yield items[:], k


def arithmetic_progression_generator(seed):
    rng = random.Random(seed)
    m = 5
    for i in range(300):
        elems = set()
        for _ in range(m):
            start = rng.randint(1, i*i + 3)
            step = rng.randint(1, 100)
            n = rng.randint(1, 10)
            for k in range(n):
                elems.add(start + k * step)
        yield sorted(list(elems))
        if i % 10 == 0:
            m += 1


def connected_islands_generator(seed):
    rng = random.Random(seed)
    for n in range(6, 100):
        for m in range(n // 2, n):
            bridges = set()
            while len(bridges) < m:
                s = rng.randint(0, n-1)
                e = rng.randint(0, n-1)
                if s != e:
                    bridges.add((s, e))
            bridges = list(bridges)
            queries = []
            while len(queries) < n:
                s = rng.randint(0, n-1)
                e = rng.randint(0, n-1)
                if s != e:
                    queries.append((s, e))
            yield n, bridges, queries


def cookie_generator(seed):
    rng = random.Random(seed)
    for i in range(40):
        items = [rng.randint(1, 2 + i)]
        for j in range(3 + i // 7):
            items.append(items[-1] + rng.randint(1, 2 + i))
        yield items


def eliminate_neighbours_generator(seed):
    rng = random.Random(seed)
    count, goal = 0, 1
    items, m = [1], 1
    for i in range(20000):
        yield items[:]
        count += 1
        if count == goal:
            count, goal = 0, goal + 3
            m = 2 + i // 100
            items = list(range(1, m))
        items.append(m)
        m += 1
        j = rng.randint(0, len(items) - 1)
        items[j], items[-1] = items[-1], items[j]


def counting_series_generator(seed):
    rng = random.Random(seed)
    curr, step = 0, 2
    for _ in range(1000):
        yield curr
        curr += rng.randint(1, step)
        step = step * 2


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


def next_zigzag_generator(seed):
    rng = random.Random(seed)
    for _ in range(100):
        for i in range(100):
            curr = rng.randint(1, 8)
            d = rng.choice([+1, -1])
            last = 0
            for j in range(i):
                last = curr % 10
                if d == -1:
                    n = rng.randint(last + 1, 9)
                else:
                    n = rng.randint(0, last - 1)
                curr = 10 * curr + n
                d = -d
            if d == -1 and last < 8:
                n = rng.randint(1, 10)
                curr = int(str(curr) + ("98" * n))
            elif d == +1 and last == 9:
                n = rng.randint(1, 10)
                curr = int(str(curr) + ("89" * n))
            yield curr


__primes = [2, 3, 5, 7, 11, 13]


def md_generator(seed):
    rng = random.Random(seed)
    for i in range(1000):
        (a, b) = rng.sample(__primes, 2)
        yield a, b, i + 2
        b = rng.randint(1, 10) * 2 + 1
        yield 2, b, i + 2


def wythoff_array_generator(seed):
    rng = random.Random(seed)
    curr, step = 1, 1
    for _ in range(300):
        yield curr
        curr += rng.randint(1, 2 * step)
        step += 1


def hourglass_flips_generator(seed):
    rng = random.Random(seed)
    for _ in range(30):
        glasses, curr = [], rng.randint(3, 20)
        n = rng.randint(2, 5)
        for j in range(n):
            glasses.append((curr, 0))
            curr += rng.randint(1, 5)
        t = rng.randint(curr + 1, 2 * curr)
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
    n, count, goal, piles = 5, 0, 3, []
    for _ in range(100):
        piles.append(rng.randint(n, n * n))
        u = rng.randint(n * n // 4, n * n)
        a = rng.randint(1, u - 1)
        b = u - a
        yield piles, a, b
        count += 1
        if count == goal:
            count, goal, n, piles = 0, goal + 5, n + 1, []


def group_and_skip_generator(seed):
    rng = random.Random(seed)
    for n in range(1, 2000):
        b = rng.randint(1, 10)
        a = 2 * b + rng.randint(1, 10)
        yield n * n, a, b


def nearest_polygonal_number_generator(seed):
    rng = random.Random(seed)
    yield from [(1, 10), (1, 100), (1, 10**100)]
    curr = 20
    for i in range(250):
        for j in range(15):
            curr = curr + rng.randint(1, curr // 10)
            s = rng.randint(3, min(curr // 3, 300))
            yield curr, s
        curr = curr * 2


def floor_power_solve_generator(seed):
    yield from [(2018, 4), (2011, 4)]
    rng = random.Random(seed)
    curr = 30
    for i in range(140):
        for j in range(10):
            curr = curr + rng.randint(1, curr // 10)
            yield curr, j + 2
        curr = curr * 2


def subtract_square_generator(seed):
    rng = random.Random(seed)
    for i in range(1, 9):
        curr = rng.randint(1, 10)
        query = []
        for j in range(4 * i):
            query.append(curr)
            curr = (4 * curr) // 3 + rng.randint(1, max(3, curr // 5))
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


def count_word_dominators_generator(seed):
    with open('words_sorted.txt', 'r', encoding='utf-8') as f:
        words = [x.strip() for x in f]
    m = 1
    wls = [[w for w in words if len(w) == n] for n in range(3, 6)]
    rng = random.Random(seed)
    for i in range(1000):
        result = rng.sample(rng.choice(wls), m)
        yield result
        result.sort(reverse=True)
        yield result
        if i % 10 == 4:
            m += 1


def hitting_integer_powers_generator():
    for b in range(3, 20):
        for a in range(2, b):
            yield a, b, 10**(2 + (a+b) % 3)


def permutation_cycles_generator(seed):
    rng = random.Random(seed)
    yield [0]
    for i in range(200):
        n = 2 + i // 10
        for _ in range(3 * i):
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
        n.append('2')
        for _ in range(rng.randint(1, 7)):
            n.append(rng.choice('123456789'))
        yield "".join(n)


def trips_fill_generator(seed):
    rng = random.Random(seed)
    with open('words_sorted.txt', encoding='UTF-8') as f:
        words3 = [word.strip() for word in f if len(word) == 4]
    for i in range(200):
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
                    yield (a, b, c),
                    yield (a, c, b),
                    yield (b, a, c),
                    yield (b, c, a),
                    yield (c, a, b),
                    yield (c, b, a),


def balanced_centrifuge_generator(seed):
    rng = random.Random(seed)
    for n in range(1, 1000):
        k = 0
        while k < n:
            yield n, k
            k += rng.randint(1, 3 + n // 30)


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
            goal = goal * 10
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
__verbs = __ar + __er + __ir
__subjects = ['yo', 'tú', 'él', 'ella', 'usted', 'nosotros', 'nosotras',
              'vosotros', 'vosotras', 'ellos', 'ellas', 'ustedes']
__tenses = ['presente', 'pretérito', 'imperfecto', 'futuro']


def conjugate_regular_generator(seed):
    rng = random.Random(seed)
    for i in range(5000):
        verb = rng.choice(__verbs)
        subject = rng.choice(__subjects)
        tense = rng.choice(__tenses)
        yield verb, subject, tense


# List of test cases for the 109 functions recognized here.

testcases = [
    # The original 109 problems. These are not in order.

    # Removed from problem set April 20, 2020
    # (
    # "connected_islands",
    # connected_islands_generator(seed),
    # "ceafc55f58a4f921582cf6fcd2c856851fca7444541e5024d1"
    # ),
    (
     "arithmetic_progression",
     arithmetic_progression_generator(fixed_seed),
     "aaab6fcefc56db92e43609036aa5bf92707f1070cdbcd96181"
    ),
    (
     "count_overlapping_disks",
     count_overlapping_disks_generator(fixed_seed),
     "58a6774be09fa37b858a375b36d5e9ce05d49eac25a5210105"
    ),
    (
     "fractional_fit",
     fractional_fit_generator(fixed_seed),
     "856627cc444098c9386367d5f250c0e2cddbf3ef0ecec3ba11"
    ),
    (
     "scylla_or_charybdis",
     scylla_or_charybdis_generator(fixed_seed),
     "7d4accab714d3d2f539450f6fcb548f56352148244b0084c6d"
    ),
    (
     "fractran",
     fractran_generator(fixed_seed),
     "4a5b2e7dee7eec27bdfdfa6748a4df2e4a06343cef38dd4ef1"
    ),
    (
     "manhattan_skyline",
     manhattan_skyline_generator(fixed_seed),
     "1e6740f53203b620e88ee42fb81b3dae5f7148cc79a1ae12d1"
    ),
    (
     "bulgarian_solitaire",
     bulgarian_solitaire_generator(fixed_seed),
     "1e9743a0ef9d4cf6025e0a6c2f60321c477772f8f757cb1de9"
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
     "459d463b7699203fa1f38496b4ba9fe4f78136ea4dc90573c7"
    ),
    (
     "forbidden_substrings",
     forbidden_substrings_generator(),
     "e2e78d63b56b3b9233e48956f3aff080e38031200c06dd3ea4"
    ),
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
     "14de088dbcfa65b452a59e4c2c624f2e090d298b68707b3a72"
    ),
    (
     "crag_score",
     crag_score_generator(),
     "ea62d9694e079b948a8b622c8f6dfd2aeebddeebc59c575721"
    ),
    (
     "unscramble",
     unscramble_generator(fixed_seed),
     "5859988a905549959fd6905cc038e0ad214812a6444d702713"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "suppressed_digit_sum",
    # suppressed_digit_sum_generator(seed),
    # "69130744180a37dae42a668f28a3aa95dd53522662e058f2cf"
    # ),
    (
     "van_eck",
     van_eck_generator(),
     "db1a6665205f46d0e80da4e1ff9926d01b33b04112013bdf43"
    ),
    (
     "domino_cycle",
     domino_cycle_generator(fixed_seed),
     "a584eae620badb493239fd0bebbfa7c8c17c12b3bc0f53f873"
    ),
    (
     "double_trouble",
     double_trouble_generator(fixed_seed),
     "49f103a7ad2c26d800d61e8645f967408a18c37cc6303a9dfc"
    ),
    (
     "nearest_smaller",
     nearest_smaller_generator(fixed_seed),
     "df87936a73650de0c707284f0dd23ec904c1f008caf46decb6"
    ),
    (
     "collatzy_distance",
     collatzy_distance_generator(fixed_seed),
     "8401965221f0d0261e2afd74afb4dbadc10045c68a5a0d72c0"
    ),
    (
     "max_checkers_capture",
     max_checkers_capture_generator(fixed_seed),
     "dd605267f7e90747c71d0df8f805030baf305c401079710772"
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
     "66a778ba1d5501bef96499ca7794a8d61534bf6b29485a64a9"
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
     "47fdebd868f35584969ccf88032830a23825b60e5da66cd776"
    ),
    (
     "count_maximal_layers",
     count_maximal_layers_generator(fixed_seed),
     "d4771768556561499dba30c0aac36a1de054dd8b424a407a93"
    ),
    (
     "square_follows",
     square_follows_generator(fixed_seed),
     "7b42ad97e654f023efeb0174c76d3f02f42a69615e90af31a3"
    ),
    (
     "extract_increasing",
     extract_increasing_generator(fixed_seed),
     "8f6ba301734d90b6a3685ae27b342ac481af80201ac35cd776"
    ),
    (
     "is_cyclops",
     is_cyclops_generator(fixed_seed),
     "5ced8d0e69d88367f1ee05f96bf6ea7fad6e1c522d0544b526"
    ),
    (
     "pyramid_blocks",
     pyramid_blocks_generator(fixed_seed),
     "9f988a1fc97c7cd92e7d358b7dd161d311c9094c66e1c78d3d"
    ),
    (
     "autocorrect_word",
     autocorrect_word_generator(),
     "29b0b30497897c0e39cca7dff294ea6b092a8b89611c2aaaeb"
    ),
    (
     "remove_after_kth",
     remove_after_kth_generator(fixed_seed),
     "3b89af0dce7e41c2fc6a851e4a35bb76f8845c5f6929ba6ade"
    ),
    (
     "seven_zero",
     seven_zero_generator(),
     "2cbae9ac1812d155ee34be3f908001b148bdf635109a38981e"
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
     random_text_generator(fixed_seed),
     "06f67d9ccd7f91b25b023d9fccd4d0622195f15f1375da16dc"
    ),
    (
     "riffle",
     riffle_generator(fixed_seed),
     "3f5df69d458a0f72fee992fda34c18139891dcc3a63d2fe372"
    ),
    (
     "ztalloc",
     ztalloc_generator(fixed_seed),
     "72c4c5bdc3a6f810e73499bb6107ac4669e947a8b80d8715f4"
    ),
    (
     "losing_trick_count",
     losing_trick_count_generator(fixed_seed),
     "814fa798f0de0d1c847b0622fc21a88047d19e427ebe1d16cf"
    ),
    (
     "postfix_evaluate",
     postfix_evaluate_generator(fixed_seed),
     "a9d473505f7a9c8458e6fbb7b3b75a56efabe1a0d3ced3d901"
    ),
    (
     "three_summers",
     three_summers_generator(fixed_seed),
     "af87ad9e569ed4f7e71379d06ce3a0c0b2cef7cc43f344ef2a"
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
     "69c94bb56d9eff5bc9cdfc4890718606c0a8bdf242c3440d98"
    ),
    (
     "count_carries",
     count_carries_generator(fixed_seed),
     "828d1619f82e852c15211efce4830fd40f8de7add7328a5bea"
    ),
    (
     "lattice_paths",
     lattice_paths_generator(fixed_seed),
     "dbca1d47adc5713b65fcb90dd9ddf1d747f521eccf341289a4"
    ),
    (
     "pancake_scramble",
     pancake_scramble_generator(fixed_seed),
     "98fb3c9e30908ea6c2654d64d3c68ca2538927be529d75ddfe"
    ),
    (
     "only_odd_digits",
     only_odd_digits_generator(fixed_seed),
     "24d656750cff73ad12fa9ff8320bbae662c2fbb5a6f4ece514"
    ),
    (
     "squares_intersect",
     squares_intersect_generator(fixed_seed),
     "6411da34d00387082aaab1845e176ccdd0558ca073f1450223"
    ),
    (
     "rooks_with_friends",
     rooks_with_friends_generator(fixed_seed),
     "305091a0a222bf14dba5c4a4883454d4e842363dcd0e696405"
    ),
    (
     "safe_squares_rooks",
     safe_squares_generator(fixed_seed),
     "5fcf5ca643f2678c51e510f5bfd1d6a7f12c180374d2f58ccb"
    ),
    (
     "safe_squares_bishops",
     safe_squares_generator(fixed_seed),
     "bc783d16964b872f62bf4a2b56b76f80c6f86c047746e87b80"
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
     "0f25a8ee2441e2c47ad5194eb4666f95fdc67d0e0fcac5b88d"
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
     "0f7e21d4668be4365ecb8c756b0cb75e514b0d51424ef6e7bc"
    ),
    (
     "words_with_given_shape",
     words_with_given_shape_generator(fixed_seed),
     "bdb3be715d5c5884d7a33914d44a2880c227bdd8543c0d9260"
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
     "bb13f872b52611a389234d48ad1a19ddea88bedb01ddb08a43"
    ),
    (
     "factoring_factorial",
     factoring_factorial_generator(fixed_seed),
     "be5d5249b396c259bde5338de73ae4d29831314d6c0fb9e369"
    ),
    (
     "bridge_hand_shorthand",
     bridge_hand_shorthand_generator(fixed_seed),
     "68459ff71e28b24e43df3f632706fabcda7403359d7d4d9255"
    ),
    (
     "milton_work_point_count",
     milton_work_point_count_generator(fixed_seed),
     "5694509170df1fef10bbb60641b7906e220d951b73d3072f7e"
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
     "e0545088966294c7048d86406e87c9ed5c5140eff279159563"
    ),
    (
     "is_perfect_power",
     is_perfect_power_generator(fixed_seed),
     "1a6d21ccd1d6b498a99e881ce50ee11a665d3a23f33084b67a"
    ),
    # Removed from problem set April 20, 2020
    # (
    # "iterated_remove_pairs",
    # iterated_remove_pairs_generator(seed),
    # "f3d6588ec3c251abfc024698c2a7371dcc7e175af1e41bb0aa"
    # ),
    # Removed from problem set August 10, 2020
    # (
    #  "detab",
    #  detab_generator(seed),
    #  "7e1453906bc31dfb59159a377dcb7dbb8451e464b88bfd04b4"
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
     "05801bf30a885839b6a2ecf760865506d1715f6461d5776f13"
    ),
    (
     "count_consecutive_summers",
     count_consecutive_summers_generator(),
     "3ade63a194b40ff5aa1b53642eee754d30f2ab48ef77330540"
    ),
    (
     "brangelina",
     brangelina_generator(fixed_seed),
     "3fa0c1ed8a374cf10a2a163eafcb10b8cf20ee97e0cbaa4de4"
    ),
    (
     "balanced_ternary",
     balanced_ternary_generator(fixed_seed),
     "5911fc03a906dc474c0d6dc168036610b0a81de5f61477d0eb"
    ),
    (
     "josephus",
     josephus_generator(fixed_seed),
     "8151ebedb3064df9721eb2a14da352beac13f0ada488998dfd"
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
    (
     "create_zigzag",
     create_zigzag_generator(fixed_seed),
     "6495896d5e3f0ed9c7f924b9f8c5c99a78700b1a5a1a6f8f98"
    ),
    (
     "calkin_wilf",
     calkin_wilf_generator(),
     "e5ff0851c0830b72802a818eeaec66711b6e3b91a004263674"
    ),
    (
     "can_balance",
     can_balance_generator(fixed_seed),
     "6d06001694009cde7c976c645acc39da4e24142e7aca3c24af"
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
    (
     "recaman",
     recaman_generator(),
     "7005741d9d236f31ebd6cdbd61f06119703aae4f8b095d1657"
    ),
    (
     "collapse_intervals",
     collapse_intervals_generator(fixed_seed),
     "e1cefd1fd979d8d50572254f8f7d7f7bbb0a0758036da2c70d"
    ),
    (
     "expand_intervals",
     expand_intervals_generator(fixed_seed),
     "5c557393fec26c62c835c85b9abc5186d6791b7770571863e8"
    ),
    (
     "reverse_ascending_sublists",
     reverse_ascending_sublists_generator(fixed_seed),
     "99877453684bc3ba3448bb939239949ffab95500fdf6c50f22"
    ),
    (
     "reverse_reversed",
     reverse_reversed_generator(fixed_seed),
     "d111344cdd8503a913181ffc7e46551b62a3dc2558a4b0fcbe"
    ),
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
     "5169c5e2252b3de7d3950c8f8802d27636c56079cf883065cb"
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
     bridge_hand_shape_generator(fixed_seed),
     "61cfd31019c2838780311603caee80a9c57fae37d4f5b561ce"
    ),
    (
     "hand_shape_distribution",
     hand_shape_distribution_generator(fixed_seed),
     "024a2e9247bc1954f922c8bbf5c6d1d2d6a549443fb86a9b0d"
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
     "f56529e27124a12b1dd52b17707a5c13fc4c8cb5c2a28bd8f5"
    ),

    # New additions to the problem set in 2020.

    (
     "cookie",
     cookie_generator(fixed_seed),
     "a04728a718656fc5367a62a61494e5a3497a64b0c3f61b7d1f"
    ),
    (
     "eliminate_neighbours",
     eliminate_neighbours_generator(fixed_seed),
     "c4ba32a3b61f74bf6d516fe419b8b036e0983451699ce6c9c7"
    ),
    (
     "counting_series",
     counting_series_generator(fixed_seed),
     "d7e9ef9de8cb71c901622aec367ff4b0eb96869cae7bbc8cd4"
    ),
    (
     "is_zigzag",
     is_zigzag_generator(fixed_seed),
     "fe5e03401a32bc5ca989759708d10a7f9d2cbd9e4821566b91"
    ),
    (
     "next_zigzag",
     next_zigzag_generator(fixed_seed),
     "52d66db24fc831dd08657f36e2e7b49ab788e6c86e8a25d3c5"
    ),
    # Removed from problem set December 17, 2020
    # (
    #  "md",
    #  md_generator(seed),
    #  "a1dcac70c093c0ba7fcfeae6d9d9655accb1cf871617f2a874"
    # ),
    (
     "wythoff_array",
     wythoff_array_generator(fixed_seed),
     "3349a1a5d59d9df74a30a2e468d369ffb0850d5b0e993c6431"
    ),
    (
     "hourglass_flips",
     hourglass_flips_generator(fixed_seed),
     "dabc24b96ab339c979f71ce837bed001ae149f3377e44f68de"
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
     "2bab761142be45af8a3a613fb553a21f227970057134ae2b22"
    ),
    (
     "group_and_skip",
     group_and_skip_generator(fixed_seed),
     "53ea5ca5bc8efee4d41805f0dd4c2629e780364f6891274896"
    ),
    (
     "nearest_polygonal_number",
     nearest_polygonal_number_generator(fixed_seed),
     "6813a79fcc5c8249e92e0bf4c1301fde4187df58d2207b23ca"
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
     "8959f61972a8804d0b26e2ae92d30d4d3fb6f08f1bcf5e28b9"
    ),
    (
     "perimeter_limit_split",
     perimeter_limit_split_generator(fixed_seed),
     "151d96f12b67f953fae52a539f669a46b734c537ed19e3ad7b"
    ),
    (
     "duplicate_digit_bonus",
     duplicate_digit_bonus_generator(fixed_seed),
     "7ad86f9210f78edbc645b2f9373f8f3f2cad9d2eaaa08fc088"
    ),
    (
     "count_word_dominators",
     count_word_dominators_generator(fixed_seed),
     "ade953572b3bf2540d892ae5d6c8912cd691305a494e3d009b"
    ),
    (
     "hitting_integer_powers",
     hitting_integer_powers_generator(),
     "ee7c93a64dd4090a231abc889da7ab6f300aa4460fdd7ff79a"
    ),
    (
     "permutation_cycles",
     permutation_cycles_generator(fixed_seed),
     "45ecf7be3ff5dbfa46a97ce660ee0484fc99baac36f55c8ad5"
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
     "c3a71cefae41fc0a49ad32ef656c68535617ad67ee4743efac"
    ),
    (
     "is_left_handed",
     is_left_handed_generator(),
     "135b781680d9b5fbbc0815ab47ef2c0646ab7970a0b1bd0e9b"
    ),
    (
     "brussels_choice_step",
     brussels_choice_step_generator(fixed_seed),
     "612cb030aeb94ef5d84d8cb973d203fccae59260e5ae4a8055"
    ),
    (
     "balanced_centrifuge",
     balanced_centrifuge_generator(fixed_seed),
     "a37b22d810035d549fc617cfe6cf72761bf9e199ad67a05485"
    ),
    (
     "lunar_multiply",
     lunar_multiply_generator(fixed_seed),
     "411dfa9dc8637871c4a257df54043301308ec7c3c09ab8ac3c"
    ),
    (
     "oware_move",
     oware_move_generator(fixed_seed),
     "f2059c85458029a78e570d44303a3255b312e49d15b68e8d2b"
    ),
    (
     "conjugate_regular",
     conjugate_regular_generator(fixed_seed),
     "aca26dc625f0f0ea10eae375e9929ed49d4ca5ea99ffb413be"
    )
]


def run_all():
    print(f"109 Python Problems tester, {version}, Ilkka Kokkarinen.")
    try:
        if version_info < (3, 7, 0):
            print("THIS SCRIPT REQUIRES PYTHON 3.7.0 OR LATER. EXITING.")
            exit(1)
        if use_record:
            # If record file exists, read the expected answers from it.
            if os.path.exists(recordfile):
                known, curr, verified = dict(), '', False
                with gzip.open(recordfile, 'rt', encoding='utf-8') as rf:
                    for line in rf:
                        line = line.strip()
                        # Special marker to indicate start of new function.
                        if line.startswith(function_prefix):
                            curr = line[len(function_prefix):]
                            known[curr] = []
                        # Special marker used to code the version information.
                        elif line.startswith(version_prefix):
                            if line[len(version_prefix):] != version:
                                print(f'VERSION MISMATCH In {recordfile} !!!!!')
                                print(f'REQUIRED: {version}')
                                print(f'ACTUAL  : {line[len(version_prefix):]}')
                                exit(2)
                            else:
                                verified = True
                        else:
                            known[curr].append(line)
                if not verified:
                    print(f"YOU ARE USING A VERY OBSOLETE VERSION OF {recordfile}. EXITING.")
                    exit(3)
                else:
                    print(f"Finished reading expected answers.")
                    test_all_functions(labs109, testcases, known=known)
            else:
                # If the record file doesn't exist, record the model answers.
                with gzip.open(recordfile, 'wt') as rf:
                    test_all_functions(labs109, testcases, recorder=rf)
        else:
            print("Testing functions without using recorded expected answers.")
            test_all_functions(labs109, testcases, known=None)
    except Exception as e:
        print(f"TESTER CRASHED WITH ERROR: {e}")
        exit(4)

# Uncomment and edit this line to look at some test cases.
# print(list(islice(remove_after_kth_generator(fixed_seed), 50)))

run_all()
