# THESE SOLUTIONS ARE NOT IN PUBLIC DOMAIN, NOR RELEASED UNDER ANY
# FREE SOFTWARE LICENSE SUCH AS GPL, MIT OR CREATIVE COMMONS.

# This file may not be distributed without the express written
# permission by Ilkka Kokkarinen, as this file is private
# intellectual property of Ilkka Kokkarinen. A small number of
# individual functions may be distributed during lab sessions
# of Python programming courses built on the material, but only
# among the official student body of that course.

from fractions import Fraction
from collections import deque, Counter
from bisect import bisect_left
from functools import lru_cache
from itertools import combinations, chain, islice, count, product, zip_longest
from datetime import timedelta
from queue import Queue
from decimal import Decimal, getcontext
from heapq import heappush, heappop, heapify


# Both lists __fibs and __primes will grow as some functions
# below are executed and need bigger Fibonacci numbers and prime
# numbers to be able to handle their larger argument values.

__fibs = [1, 2, 3, 5, 8, 13, 21, 34, 55]

__primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101]

# The following lists of things will remain fixed throughout the execution.

__faces = {14: 'A', 13: 'K', 12: 'Q', 11: 'J'}

__suits = ['spades', 'hearts', 'diamonds', 'clubs']

__losers = {
    '-': 0, 'A': 0, 'x': 1, 'Q': 1, 'K': 1, 'AK': 0, 'AQ': 1, 'Ax': 1,
    'KQ': 1, 'Kx': 1, 'Qx': 2, 'xx': 2, 'AKQ': 0, 'AKx': 1, 'AQx': 1,
    'Axx': 2, 'Kxx': 2, 'KQx': 1, 'Qxx': 2, 'xxx': 3
}

__bridge_ranks = {
    'two': 2, 'three': 3, 'four': 4, 'five': 5, 'six': 6, 'seven': 7, 'eight': 8, 'nine': 9,
    'ten': 10, 'jack': 11, 'queen': 12, 'king': 13, 'ace': 14
}

__gin_ranks = {
    'ace': 1, 'two': 2, 'three': 3, 'four': 4, 'five': 5, 'six': 6, 'seven': 7, 'eight': 8,
    'nine': 9, 'ten': 10, 'jack': 11, 'queen': 12, 'king': 13
}

__morse = {
    '.-': 'a', '-...': 'b', '-.-.': 'c', '-..': 'd', '.': 'e', '..-.': 'f', '--.': 'g', '....': 'h',
    '..': 'i', '.---': 'j', '-.-': 'k', '.-..': 'l', '--': 'm', '-.': 'n', '---': 'o', '.--.': 'p',
    '--.-': 'q', '.-.': 'r', '...': 's', '-': 't', '..-': 'u', '...-': 'v', '.--': 'w', '-..-': 'x',
    '-.--': 'y', '--..': 'z'
}

__morse_r = {__morse[k]: k for k in __morse}

__lowest_unseen = 0
__diffs_taken = set()
__mian_chowla = [1]

__prev_recaman = 0
__lowest_unseen_rec = 1
__recaman_seen = set()

__diamond_total = 1
__diamond_lowest_unseen = 2
__diamond_seen = {1}

__sv_prev = 1
__sv_lowest_unseen = 2
__sv_seen = {1}
__sv_lowest_diff = 0
__sv_diff_seen = set()

__knight_moves = [(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]
__king_moves = [(0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1)]

__zero = Fraction(0)
__one = Fraction(1)
__one_eighth = Fraction(1, 8)
__one_half = Fraction(1, 2)

__hof_r = [1]
__hof_s = [2]
__hof_missing = 4
__hof_idx = 0

__kim_left = []
__kim_right = 1

__rr_seq = '0'
__rr_max = 0

__gijswijt = [1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1]

__factorials = [1]

__ordinals = ['zeroth', 'first', 'second', 'third', 'fourth', 'fifth', 'sixth', 'seventh', 'eighth', 'ninth', 'tenth']
__removals = ['none', 'once', 'twice', 'thrice', 'four times', 'five times', 'six times', 'seven times',
              'eight times', 'nine times', 'ten times']

# Fill in the factorials list as needed.

def __fact(n):
    while len(__factorials) < n + 1:
        __factorials.append(len(__factorials) * __factorials[-1])
    return __factorials[n]


def sign(n):
    if n < 0:
        return -1
    elif n > 0:
        return +1
    else:
        return 0

# The actual solution functions. These are not in any particular order.

def merge_biggest(items):
    items = [-e for e in items]
    heapify(items)
    while len(items) > 1:
        a = heappop(items)
        b = heappop(items)
        c = abs(a - b)
        if c > 0:
            heappush(items, -c)
    return -items[0] if len(items) > 0 else 0


def maximum_word_select(words, letters):
    n = len(words)
    letters_remain = Counter(letters)
    word_order = sorted(range(n), key=lambda i: (len(words[i]), i), reverse=True)
    letter_count = [Counter(word) for word in words]
    best = 0

    def recurse(d, score_so_far):
        nonlocal best
        best = max(best, score_so_far)
        if d == n:
            return
        i = word_order[d]
        # Try to take in this word
        if letter_count[i] <= letters_remain:
            letters_remain.subtract(words[i])
            recurse(d + 1, score_so_far + len(words[i]))
            letters_remain.update(words[i])
        # Leave out this word
        recurse(d + 1, score_so_far)

    recurse(0, 0)
    return best


def generalized_fibonacci(multipliers, n):
    k = len(multipliers)
    values = [1 for _ in range(k)]
    for _ in range(n - k + 1):
        v = 0
        for i in range(-1, -(k+1), -1):
            v += multipliers[i] * values[i]
        values.append(v)
    return values[-1]

print([generalized_fibonacci((1, 1), k) for k in range(2, 20)])

def sultans_daughter(digits):

    def sultan_eval(dig):
        if len(dig) < 1:
            return None
        if dig[0] == '1' and dig[-1] == '2':
            return dig[1:-1]
        r = sultan_eval(dig[1:])
        if r is None:
            return None
        if dig[0] == '3':
            return r + r
        elif dig[0] == '4':
            return r[::-1]
        elif dig[0] == '5':
            return r[1:]
        elif dig[0] == '6':
            return f"1{r}"
        elif dig[0] == '7':
            return f"2{r}"
        else:
            return None

    seen, total = {digits}, 0
    while digits:
        digits = sultan_eval(digits)
        total += 1
        if digits in seen:
            return -1
        seen.add(digits)
    return total


def partition_point(items):
    n = len(items)
    n2 = n // 2
    mins = [0 for _ in range(n)]
    mins[n - 1] = items[n - 1]
    for i in range(n - 2, -1, -1):
        mins[i] = min(items[i], mins[i + 1])
    big = min(items) - 1
    best_i = -1
    for i, e in enumerate(items, 1):
        big = max(big, e)
        if i < n - 1 and big <= mins[i] and abs(n2 - i) < abs(n2 - best_i):
            best_i = i
    return best_i


def sturm_word(x, y):
    if y > x:
        return "".join('0' if c == '1' else '1' for c in sturm_word(y, x))
    result, prev_y, yy, slope = "", 0, 0, Fraction(y, x)
    for xx in range(1, x):
        yy += slope
        yy_floor = yy.numerator // yy.denominator
        if yy_floor > prev_y:
            result += "1"
            prev_y = yy_floor
        result += "0"
    return result


def double_ended_pop(items, k):
    # Take everything from right
    best = s = sum(items[-k:])
    for i in range(k):
        # Take one more item from left
        s = s + items[i] - items[-k + i]
        best = max(best, s)
    return best


def palindrome_split(text):
    n = len(text)
    table = [0 for _ in range(n + 1)]
    for i in range(n - 1, -1, -1):
        best = 0
        for j in range(i + 1, n + 1):
            ii, jj = i, j - 1
            while ii < jj and text[ii] == text[jj]:
                ii, jj = ii + 1, jj - 1
            if ii >= jj:
                best = max(best, (j - i) * (j - i) + table[j])
        table[i] = best
    return table[0]


def assign_sides(costs):
    n = len(costs) // 2
    costs.sort(key=lambda x:x[0] - x[1])
    return sum(a for (a, _) in costs[:n]) + sum(b for (_, b) in costs[n:])


def colonel_blotto(friend, enemy, prize):
    n = len(friend)
    friend.sort(reverse=True)
    friend.append(0)
    # Set up dancing links structure for remaining friend units.
    pred = [i-1 for i in range(n+1)]
    succ = [i+1 for i in range(n+1)]
    pred[0] = n
    succ[n] = 0

    best = 0
    order = sorted(range(n), key=lambda i:(prize[i], i), reverse=True)
    remain = [0 for _ in range(n+1)]
    for i in range(n-1, -1, -1):
        remain[i] = remain[i+1] + prize[order[i]]

    def recurse(d, score):
        nonlocal best
        best = max(best, score)
        if d == n or score + remain[d] <= best:
            return
        p = order[d]

        # Try to win this battlefield, assign the weakest unit that still wins.
        u, v = succ[n], n
        while friend[u] > enemy[p]:
            v, u = u, succ[u]
        if friend[v] > enemy[p]:
            succ[pred[v]] = succ[v]
            pred[succ[v]] = pred[v]
            recurse(d + 1, score + prize[p])
            pred[succ[v]] = v
            succ[pred[v]] = v
        # Lose this battlefield, assign the weakest remaining unit.
        v = pred[n]
        if friend[v] < enemy[p]:
            succ[pred[v]] = succ[v]
            pred[succ[v]] = pred[v]
            recurse(d + 1, score)
            pred[succ[v]] = v
            succ[pred[v]] = v

    recurse(0, 0)
    return best


def maximal_cliques(edges):
    n = len(edges)
    cliques = []

    def bron_kerbosch(r, p, x):
        if len(r) > 2 and not p and not x:
            cliques.append(sorted(r))
        u = None
        for w in sorted(p | x):
            if u is None or len(edges[w]) > len(edges[u]):
                u = w
        if u is not None:
            for v in list(p - set(edges[u])):
                ev = set(edges[v])
                bron_kerbosch(r | {v}, p & ev, x & ev)
                p.remove(v)
                x.add(v)

    bron_kerbosch(set(), set(range(n)), set())
    return sorted(cliques, key=lambda e: (-len(e), e))


def chunk_sorting(perm):
    total, big = 0, 0
    for (i, e) in enumerate(perm):
        big = max(big, e)
        total += big == i
    return total


def bays_durham_shuffle(items, k):
    result = []
    table = [next(items) for _ in range(k)]
    try:
        while True:
            e = next(items)
            result.append(table[e % k])
            table[e % k] = e
    except StopIteration:
        return result


def maximal_repeated_suffix(items):
    n = len(items)
    m = n // 2
    while m > 0:
        for i in range(m):
            if items[-2 * m + i] != items[-m + i]:
                break
        else:
            return m
        m -= 1
    return 0


def count_slices_with_sum(items, goal):
    n = len(items)
    i, j, total, curr_sum = 0, 0, 0, items[0]
    while True:
        if curr_sum == goal:
            total += 1
        if i == j or curr_sum < goal:
            j += 1
            if j == n:
                return total
            curr_sum += items[j]
        else:
            curr_sum -= items[i]
            i += 1


def count_increasing_paths(matrix):
    n = len(matrix)
    prev = [[1 for _ in range(n)] for _ in range(n)]
    curr = [[0 for _ in range(n)] for _ in range(n)]
    total = 0
    while any(any(prev[x]) for x in range(n)):
        for (x, y) in product(range(n), repeat=2):
            curr[x][y] = 0
            for (dx, dy) in [(0, 1), (1, 0), (0, -1), (-1, 0)]:
                xx, yy = x + dx, y + dy
                if 0 <= xx < n and 0 <= yy < n and matrix[xx][yy] < matrix[x][y]:
                    curr[x][y] += prev[xx][yy]
        curr, prev = prev, curr
        total += sum(curr[x][y] for (x, y) in product(range(n), repeat=2))
    return total


def slater_velez(k):
    global __sv_prev, __sv_lowest_unseen, __sv_lowest_diff
    n = __sv_lowest_unseen
    m = __sv_lowest_diff
    p = __sv_prev
    if p > n and p - n < m:
        n = p + m
    elif p < n:
        n = max(n, p + m)
    while True:
        d = abs(n - p)
        if n in __sv_seen or d < __sv_lowest_diff or d in __sv_diff_seen:
            n += 1
        else:
            break
    __sv_prev = n
    __sv_seen.add(n)
    while __sv_lowest_unseen in __sv_seen:
        __sv_seen.remove(__sv_lowest_unseen)
        __sv_lowest_unseen += 1
    __sv_diff_seen.add(d)
    while __sv_lowest_diff in __sv_diff_seen:
        __sv_diff_seen.remove(__sv_lowest_diff)
        __sv_lowest_diff += 1
    return n


def diamond_sequence(k):
    global __diamond_lowest_unseen, __diamond_total
    n = k - (__diamond_total % k)
    while True:
        if n < __diamond_lowest_unseen or n in __diamond_seen:
            n += k
        __diamond_seen.add(n)
        while __diamond_lowest_unseen in __diamond_seen:
            __diamond_seen.remove(__diamond_lowest_unseen)
            __diamond_lowest_unseen += 1
        __diamond_total += n
        return n


def multiple_winner_election(votes, seats, method):
    n = len(votes)
    if method == "dhondt":
        f = lambda v, s: Fraction(v, s + 1)
    elif method == "webster":
        f = lambda v, s: Fraction(v, 2 * s + 1)
    else:  # Imperiali
        f = lambda v, s: Fraction(v, 1) / (1 + Fraction(s, 2))
    result = [0 for _ in range(n)]
    priority = [f(v, 0) for v in votes]
    for _ in range(seats):
        m = 0
        for i in range(1, n):
            if priority[i] > priority[m]:
                m = i
        result[m] += 1
        priority[m] = f(votes[m], result[m])
    return result


def pebblery(prev):
    n = len(prev)
    seen = dict()
    best = n + 1
    succ_mask = [0 for _ in range(n)]
    for i in range(n):
        for j in prev[i]:
            succ_mask[i] |= (1 << (2*j+1))

    def recurse(state, max_pebbles, pebbles, tabu):
        assert max_pebbles >= pebbles
        nonlocal best
        if max_pebbles >= best or seen.get(state, n) <= max_pebbles:
            return
        seen[state] = max_pebbles
        for i in range(n):
            # Try adding pebble to position i if you can
            if tabu != i and state & (1 << 2*i) == 0 and all(state & (1 << 2*j) for j in prev[i]):
                if i == 0:  # Goal reached, pebble in root sink
                    best = max_pebbles
                    return
                recurse((state | (1 << 2*i) | (1 << (2*i+1))) & ~succ_mask[i],
                        max(max_pebbles, pebbles + 1), pebbles + 1, -1)
            # Try removing pebble from position i if you can
            elif state & (1 << 2*i) != 0 and state & (1 << (2*i+1)) == 0:
                recurse(state & ~(1 << 2*i), max_pebbles, pebbles - 1, i)

    best = n + 1
    recurse(0, 0, 0, -1)
    return best


def poker_test(seq):
    n, counts = len(seq), [0, 0, 0, 0, 0, 0, 0]
    for i in range(n - 4):
        # Count the number of internal pairs
        pairs = sum(a == b for (a, b) in combinations(sorted(seq[i:i+5]), 2))
        if pairs == 10:   # Five of a kind
            counts[0] += 1
        elif pairs == 6:  # Four of a kind
            counts[1] += 1
        elif pairs == 4:  # Full house
            counts[2] += 1
        elif pairs == 3:  # Three of a kind
            counts[3] += 1
        elif pairs == 2:  # Two pair
            counts[4] += 1
        elif pairs == 1:  # One pair
            counts[5] += 1
        else:  # High card
            assert pairs == 0
            counts[6] += 1
    return counts


def is_semiconnected(edges):
    n = len(edges)
    reach = [[False for _ in range(n)] for _ in range(n)]
    for i, e in enumerate(edges):
        reach[i][i] = True
        for j in e:
            reach[i][j] = True
    for k in range(1, n):
        for i in range(n):
            for j in range(n):
                reach[i][j] = reach[i][j] or (reach[i][k-1] and reach[k-1][j])
    return all(reach[i][j] or reach[j][i] for (i, j) in combinations(range(n), 2))


def post_correspondence_problem(aa, bb, lo, hi):

    def recurse(first, second):
        nonlocal aa, bb
        fn, sn = len(first), len(second)
        if fn > hi or sn > hi:
            return False
        if lo <= fn == sn <= hi:
            return True
        if fn == sn > 0 and lo -(lo % fn) + fn <= hi:
            return True
        switched = False
        if fn > sn:  # Ensure that first string is not longer than second.
            switched = True
            fn, sn, first, second, aa, bb = sn, fn, second, first, bb, aa
        for (a, b) in zip(aa, bb):
            over = second[fn:]
            if over.startswith(a) or a.startswith(over):
                first2 = first + a
                fn2 = len(first2)
                if fn2 > sn:
                    over = first2[sn:]
                    if not (over.startswith(b) or b.startswith(over)):
                        continue
                if recurse(first2, second + b):
                    return True
        if switched:  # Switch back before returning
            fn, sn, first, second, aa, bb = sn, fn, second, first, bb, aa
        return False

    return recurse("", "")


def zeckendorf_decode(fits):
    result, a, b, curr, prev_f = [], 1, 1, 0, 0
    for f in fits:
        if f == '1':
            if prev_f == '1':
                result.append(curr)
                a, b, curr, f = 0, 1, 0, 0
            else:
                curr += b
        prev_f, a, b = f, b, a + b
    return result


def average_run_length(items):
    run_sum, run_count, d, curr, prev, ch = 0, 0, 0, 1, None, 0
    for e in items:
        if prev is not None:
            ch = sign(e - prev)
            if d == 0:
                d = ch
                curr += 1
            elif ch == d or ch == 0:
                curr += 1
            else:
                run_sum += curr
                run_count += 1
                curr = 2
                d = ch
        prev = e
    if curr > 1:
        run_sum += curr
        run_count += 1
    return Fraction(run_sum, run_count)


def fourth_seat_opening(hand):
    points, values = 0, {'ace': 4, 'king': 3, 'queen': 2, 'jack': 1}
    for (rank, suit) in hand:
        points += values.get(rank, 0)
    counts = bridge_hand_shape(hand)

    if points + counts[0] >= 15:
        return True

    return points > 9 and (counts[0] >= 6 or counts[1] >= 6 or counts[2] >= 7 or counts[3] >= 7)


# Superior solution created by Claude Opus 4.

def front_back_sort(perm):
    """
    Find minimum number of moves needed to sort a permutation,
    where each move takes an element to the front or back.

    Key insight: Find the longest contiguous subsequence of consecutive
    integers that appear in increasing order. These don't need to move.

    Uses DP: dp[i] = length of longest sequence ending at value i
    """
    n = len(perm)

    # dp[i] = length of longest contiguous sequence ending with value i
    dp = [1] * n

    # pos[i] gives the position where value i appears
    pos = [0] * n
    for i in range(n):
        pos[perm[i]] = i

    max_length = 1

    # For each value from 1 to n-1
    for val in range(1, n):
        # If val appears after val-1, we can extend the sequence
        if pos[val] > pos[val - 1]:
            dp[val] = dp[val - 1] + 1
            max_length = max(max_length, dp[val])

    # The answer is n minus the longest subsequence we can keep
    return n - max_length


def pick_it(items):
    n = len(items)
    # Initialize the dancing links node list for items that have been taken
    succ = [i + 1 for i in range(n)]
    pred = [i - 1 for i in range(n)]
    succ[n - 1] = 0
    pred[0] = n - 1
    best = sum(-(x*x) for x in items)

    def recurse(so_far):
        nonlocal best
        if succ[0] == n - 1:
            best = max(best, so_far)
        else:
            i = succ[0]
            while i < n - 1:
                # Try taking out item in position i
                pred[succ[i]] = pred[i]
                succ[pred[i]] = succ[i]
                recurse(so_far + items[pred[i]]**2 + items[i] - items[succ[i]]**2)
                # Downdate to restore that item
                succ[pred[i]] = i
                pred[succ[i]] = i
                i = succ[i]

    recurse(0)
    return best


def find_all_words(letters, words):
    n = len(letters)
    # Initialize the dancing links node list for letters that have been taken
    succ = [i + 1 for i in range(n+1)]
    pred = [i - 1 for i in range(n+1)]
    succ[n] = 0
    pred[0] = n
    result = []

    def is_word(word):
        i = bisect_left(words, word)
        return i < len(words) and words[i] == word

    def starts_word(word):
        i = bisect_left(words, word)
        return i < len(words) and words[i].startswith(word)

    def recurse(word_sofar):
        if is_word(word_sofar):
           result.append(word_sofar)
        elif not starts_word(word_sofar):
            return
        prev = '$'
        i = succ[n]
        while i < n:
            if letters[i] != prev:
                pred[succ[i]] = pred[i]
                succ[pred[i]] = succ[i]
                prev = letters[i]
                recurse(word_sofar + prev)
                succ[pred[i]] = i
                pred[succ[i]] = i
            i = succ[i]

    recurse("")
    return result


def optimal_ab_filling(text, ab, ba):
    n = len(text)
    vv = n * max(ab, ba)

    lru_cache(maxsize=2*n)
    def recurse(i, prev):
        v = vv
        if i == n:
            return 0
        if text[i] != 'b':  # Try 'a' in the current position
            v = recurse(i + 1, 'a') + (ba if prev == 'b' else 0)
        if text[i] != 'a':  # Try 'b' in the current position
            v = min(v, recurse(i + 1, 'b') + (ab if prev == 'a' else 0))
        return v

    return recurse(0, '$')


def haircut(speed, n):
    m = len(speed)
    time_left = [0 for _ in range(m)]
    for _ in range(n):
        i = 0
        for j in range(1, m):
            if time_left[j] < time_left[i]:
                i = j
        min_time = time_left[i]
        if min_time > 0:
            for j in range(m):
                time_left[j] -= min_time
        time_left[i] = speed[i]
    return i


def limited_swaps(perm, swaps):
    expected = sorted(perm)
    if perm == expected:
        return perm

    best = perm[:]

    def distance(p):
        return sum(e == i for (i, e) in enumerate(p))

    queue, seen = [(distance(perm), perm)], set()
    while len(queue) > 0:
        p = heappop(queue)
        for (i, j) in swaps:
            (_, p2) = p[:]
            p2[i], p2[j] = p2[j], p2[i]
            p2s = str(p2)
            if p2s not in seen:
                if p2 == expected:
                    return p2
                if p2 < best:
                    best = p2[:]
                heappush(queue, (distance(p2), p2))
                seen.add(p2s)
    return best


def bayes_dice_update(dice, rolls):
    n = len(dice)
    probs = [Fraction(1, n) for _ in dice]
    for r in rolls:
        for (i, d) in enumerate(dice):
            if r <= d:
                probs[i] = probs[i] * Fraction(1, d)
            else:
                probs[i] = 0
    s = sum(probs)
    return [p / s for p in probs]


def s_eval(expr):
    stack, reading_number, num = [], False, 0
    for c in chain(expr, '$'):
        if reading_number and c not in '0123456789':
            stack.append(num)
            num = 0
            reading_number = False
        if c in '0123456789':
            reading_number = True
            num = 10 * num + int(c)
        elif c in "+-*":
            stack.append(c)
        elif c == ')':
            b = stack.pop()
            a = stack.pop()
            op = stack.pop()
            if op == '+':
                stack.append(a + b)
            elif op == '-':
                stack.append(a - b)
            elif op == '*':
                stack.append(a * b)
            else:
                raise ValueError("Illegal expression")
        else:
            pass  # Skip all other characters
    return stack[0]


def odds_and_evens(first, second):
    n, m = len(first), len(second)

    @lru_cache(maxsize = n * n * m * m)
    def recurse(odd, even, fm, sm, i, j):
        if i == n and j == m:
            return max(fm, sm)
        best = 10 * (n + m)
        if i < n:
            if first[i] == '0':
                fmm = max(even + 2, fm + (1 if fm % 2 else 2))
                best = min(best, recurse(odd, fmm, fmm, sm, i + 1, j))
            else:
                fmm = max(odd + 2, fm + (2 if fm % 2 else 1))
                best = min(best, recurse(fmm, even, fmm, sm, i + 1, j))
        if j < m:
            if second[j] == '0':
                smm = max(even + 2, sm + (1 if sm % 2 else 2))
                best = min(best, recurse(odd, smm, fm, smm, i, j + 1))
            else:
                smm = max(odd + 2, sm + (2 if sm % 2 else 1))
                best = min(best, recurse(smm, even, fm, smm, i, j + 1))
        return best

    return recurse(-1, 0, -1, -1, 0, 0)


def cousin_explainer(a, b):
    sa, sb = 0, 0
    # Climb up on step from larger number until both numbers are equal
    while a != b:
        if a > b:
            sa, a = sa + 1, a // 2
        else:
            sb, b = sb + 1, b // 2
    if sb == 0:  # Parental line
        return 'mother' if sa == 1 else ('great ' * (sa - 2)) + 'grandmother'
    elif sa == 0:  # Descendant line
        return 'daughter' if sb == 1 else ('great ' * (sb - 2)) + 'granddaughter'
    elif sa == 1:  # Sisterly line
        if sb == 1:
            return 'sister'
        else:
            return 'niece' if sb == 2 else ('great ' * (sb - 2)) + 'grandniece'
    elif sb == 1:  # Aunty line
        if sa == 2:
            return 'aunt'
        elif sa == 3:
            return 'great aunt'
        else:
            return ('great ' * (sa - 3)) + 'grandaunt'
    else:  # Cousinly line
        cousin_degree = __ordinals[min(sa, sb) - 1]
        cousin_removal = __removals[abs(sa - sb)]
        return f'{cousin_degree} cousin' if sa == sb else f'{cousin_degree} cousin {cousin_removal} removed'


def lehmer_encode(perm):
    result, n = [], len(perm)
    for i in range(n - 1):
        inv = 0
        for j in range(i + 1, n):
            if perm[j] < perm[i]:
                inv += 1
        result.append(inv)
    return result


def lehmer_decode(inv):
    n = len(inv) + 1
    perm = [0 for _ in range(n)]
    taken = [False for _ in range(n)]
    for i, c in enumerate(inv):
        m = 0
        while c >= 0:
            if not taken[m]:
                c -= 1
            if c >= 0:
                m += 1
        taken[m] = True
        perm[i] = m
    assert not all(taken)
    for i, e in enumerate(taken):
        if not e:
            perm[n - 1] = i
            return perm
    assert False  # Unreachable


def loopless_walk(steps):
    result, seen = [], dict()
    for c in steps:
        if seen.get(c, 0) == 0:
            result.append(c)
            seen[c] = 1
        else:
            while result[-1] != c:
                seen[result.pop()] -= 1
    return "".join(result)


def square_root_sum(n1, n2):
    precision = 20
    while True:
        getcontext().prec = precision
        n1_sum = sum(Decimal(n).sqrt() for n in n1)
        n2_sum = sum(Decimal(n).sqrt() for n in n2)
        n1s = str(n1_sum)
        n2s = str(n2_sum)
        while len(n1s) < len(n2s):
            n1s += "0"
        while len(n2s) < len(n1s):
            n2s += "0"
        i = 0
        while i < len(n1s) and n1s[i] == n2s[i]:
            i += 1
        if len(n1s) - i > 5:
            return n1_sum > n2_sum
        precision += 10


def friendship_paradox(friends):
    n = len(friends)
    avg_friends = Fraction(sum(len(f) for f in friends), n)
    fa_total = 0
    for fs in friends:
        f_total = sum(len(friends[f]) for f in fs)
        fa_total += Fraction(f_total, len(fs))
    avg_ff = Fraction(fa_total, n)
    # Check that the second average is not smaller than the first one before returning both.
    assert avg_ff >= avg_friends
    return avg_friends, avg_ff


def factoradic_base(n):
    result, k, f, n_orig = [], 1, 1, n
    # Find the largest factorial that is at most equal to n.
    while f < n:
        k += 1
        f = f * k
    if f > n:
        f = f // k
        k -= 1
    # Compute the coefficients from the highest factorial down.
    for _ in range(k):
        result.append(n // f)
        n = n % f
        f = f // k
        k -= 1
    result = result[::-1]
    # Just to be safe, verify that decoding the result produces the original n.
    total, f = 0, 1
    for k, c in enumerate(result):
        f = f * (k + 1)
        total += c * f
    assert total == n_orig
    return result


def tchuka_ruma(board):
    n, m, best = len(board), sum(board), 0

    def move(pos, undo_stack):
        while True:
            assert pos > 0
            pebbles = board[pos]
            board[pos] = 0
            undo_stack.append(pebbles)
            while pebbles > 0:
                pos = (pos - 1) % n
                board[pos] += 1
                pebbles -= 1
            if pos == 0:
                return 0    # Successful move
            if board[pos] == 1:
                return pos  # Game ends with this move


    def undo_move(pos, undo_stack):
        while len(undo_stack) > 0:
            pebbles = undo_stack.pop()
            for _ in range(pebbles):
                board[pos] -= 1
                pos = (pos + 1) % n
            board[pos] += pebbles


    def play():
        nonlocal best
        if best == m:
            return
        undo_stack = []
        for pos in range(1, n):
            if board[pos] > 0:
                end_pos = move(pos, undo_stack)
                best = max(best, board[0])
                if end_pos == 0:
                    play()
                undo_move(end_pos, undo_stack)

    play()
    return best


def gauss_circle(r):
    total, x, y, rr = 0, 0, r, r * r
    while y >= 0:
        total += 2 * x + 1
        if y > 0:
            total += 2 * x + 1
        y -= 1
        while x*x + y*y <= rr:
            x += 1
        x -= 1
    return total


def maximum_palindrome(digits):
    occurs = [digits.count(d) for d in "0123456789"]
    highest_odd = max(chain([i for i in range(10) if occurs[i] % 2], [-1]))
    result = "".join(str(d) * (occurs[d] // 2) for d in range(9, 0, -1))
    if len(result) > 0:
        result += "0" * (occurs[0] // 2)
    result += (str(highest_odd) if highest_odd > -1 else "") + result[::-1]
    return int(result) if result else 0


def ants_on_the_rod(ants, w):
    n = len(ants)
    lo, hi, t = 0, n - 1, 0
    falloff = [0 for _ in range(n)]
    while lo <= hi:
        skip = -1
        for i in range(lo, hi + 1):
            if i == skip:
                continue
            if i == lo and ants[i][1] == -1:
               falloff[i] = t + ants[i][0]
               ants[i][0] = -1
               lo += 1
            elif i == hi and ants[i][1] == +1:
               falloff[i] = t + w - ants[i][0]
               ants[i][0] = w + 1
               hi -= 1
            elif ants[i][1] == -1:
                ants[i][0] -= 1
                if ants[i - 1][0] == ants[i][0]:
                    ants[i - 1][1] = -1
                    ants[i][1] = +1
            else:
                if ants[i + 1][1] == -1 and ants[i][0] + 1 == ants[i + 1][0]:
                    ants[i][1] = -1
                    ants[i + 1][1] = +1
                    skip = i + 1
                    if ants[i - 1][0] == ants[i][0]:
                        ants[i - 1][1] = -1
                        ants[i][1] = +1
                else:
                    ants[i][0] += 1
        t += 1

    # Just to be safe, verify that the result list has "organ pipe" shape
    prev, descended = 0, False
    for e in falloff:
        assert e <= w
        diff = e - prev
        assert not descended or diff <= 0
        if diff < 0:
            descended = True
    # Okay to return
    return falloff


def multiply_and_sort(n, mul):
    seen, top = set(), n
    while n not in seen:
        seen.add(n)
        n = int("".join(sorted(d for d in str(mul * n))))
        top = max(n, top)
    return top


def split_at_none(items):
    result, current = [], []
    for e in chain(items, [None]):
        if e is None:
            result.append(current)
            current = []
        else:
            current.append(e)
    return result


def magic_knight(n, items):
    board = [[None for _ in range(n)] for _ in range(n)]
    result = []
    m, p, x, y = 1, 0, n - 1, n - 1
    while True:
        board[x][y] = m
        if items[p] == m:
            result.append((x, y))
            p += 1
            if p == len(items):
                return result
        m += 1
        x = x - 1 if x > 0 else n - 1
        y = y - 2 if y > 1 else n + (y - 2)
        if board[x][y] is not None:
            x = x - 2 if x > 1 else n + (x - 2)
        if board[x][y] is not None:
            print(f"Repeated square {x=} {y=}")
            assert False


def power_prefix(prefix):
    p, k = 1, 0
    while True:
        pp = str(p)
        if len(pp) >= len(prefix) and all(dd == '*' or pd == dd for (pd, dd) in zip(pp, prefix)):
            return k
        p, k = 2 * p, k + 1

# Superior solution provided by Claude Sonnet 3.5.

def pinch_moves(board, player):
    """
    Generates all legal next board states for the given player in 1D Go ("pinch").

    Args:
        board (str): The current board state ('W', 'B', '.', 'R').
        player (str): The current player ('W' or 'B').

    Returns:
        list[str]: A list of unique board states representing legal next moves.
                   Each string is the board *after* the move and captures,
                   with 'R' points reset to '.' for the next turn.
    """
    n = len(board)
    opponent = 'B' if player == 'W' else 'W'
    possible_next_boards = set()  # Use a set to automatically handle duplicates

    # --- Helper function to resolve captures ---
    def resolve_captures(current_board_list, capturer_color):
        """
        Identifies and removes captured groups of the opponent.

        Args:
            current_board_list (list[str]): The board state as a list of characters.
            capturer_color (str): The player whose move might cause captures.

        Returns:
            tuple[list[str], bool]: A tuple containing:
                - The board state (list) after captures, with captured stones marked 'R'.
                - A boolean indicating if any captures were made.
        """
        board_after_capture = list(current_board_list)  # Work on a copy
        captured_something = False
        target_color = 'B' if capturer_color == 'W' else 'W'
        length = len(board_after_capture)
        i = 0
        while i < length:
            if board_after_capture[i] == target_color:
                # Found start of a potential opponent group
                group_start = i
                j = i
                while j < length and board_after_capture[j] == target_color:
                    j += 1
                group_end = j - 1  # Inclusive index of the last piece in the group

                # Check if the group is surrounded
                left_surrounded = (group_start == 0) or \
                                  (board_after_capture[group_start - 1] == capturer_color)
                right_surrounded = (group_end == length - 1) or \
                                   (group_end + 1 < length and board_after_capture[group_end + 1] == capturer_color)

                if left_surrounded and right_surrounded:
                    captured_something = True
                    # Mark the captured group with 'R'
                    for k in range(group_start, group_end + 1):
                        board_after_capture[k] = 'R'
                    i = group_end + 1  # Continue search after the captured group
                else:
                    i = group_end + 1  # Continue search after the non-captured group
            else:
                i += 1
        return board_after_capture, captured_something

    # --- Helper function to check if a specific group is captured ---
    def is_group_captured(board_state_list, group_start, group_end, group_color):
        """Checks if a specific group is currently captured (surrounded)."""
        length = len(board_state_list)
        potential_capturer = 'B' if group_color == 'W' else 'W'

        left_surrounded = (group_start == 0) or \
                          (group_start > 0 and board_state_list[group_start - 1] == potential_capturer)
        right_surrounded = (group_end == length - 1) or \
                           (group_end < length - 1 and board_state_list[group_end + 1] == potential_capturer)

        return left_surrounded and right_surrounded

    # --- Helper function to find the group containing a given index ---
    def find_group(board_state_list, index):
        """Finds the start and end indices of a contiguous group containing index."""
        piece = board_state_list[index]
        if piece == '.' or piece == 'R':
            return -1, -1  # Not part of a solid group

        start = index
        while start > 0 and board_state_list[start - 1] == piece:
            start -= 1

        end = index
        length = len(board_state_list)
        while end < length - 1 and board_state_list[end + 1] == piece:
            end += 1

        return start, end

    # --- Iterate through all possible move positions ---
    for i in range(n):
        original_char_at_i = board[i]

        # Rule: Can only play on '.' or 'R'
        if original_char_at_i == '.' or original_char_at_i == 'R':
            # 1. Simulate placing the stone
            board_list_after_placement = list(board)
            board_list_after_placement[i] = player

            # 2. Resolve captures of the opponent caused by this move
            board_list_after_opponent_capture, opponent_captured = resolve_captures(
                board_list_after_placement, player
            )

            # 3. Check the special 'R' point rule:
            #    Playing on 'R' is illegal *if* it captures an opponent group.
            if original_char_at_i == 'R' and opponent_captured:
                continue  # This move is illegal, skip to next potential position

            # 4. Check for suicide:
            #    A move is suicide if it results in the newly placed stone's group
            #    being captured, AND no opponent stones were captured by the move.
            is_suicide = False
            if not opponent_captured:
                # Find the group the newly placed stone belongs to *after* opponent captures
                # (which didn't happen in this case, but use the intermediate board state)
                group_start, group_end = find_group(board_list_after_opponent_capture, i)

                # If find_group returned valid indices (i.e., the spot wasn't immediately marked 'R' - shouldn't happen here)
                # Check if this group is now surrounded by the opponent
                if group_start != -1:
                    if is_group_captured(board_list_after_opponent_capture, group_start, group_end, player):
                        is_suicide = True

            # 5. If the move is not suicide, it's a legal move.
            if not is_suicide:
                # The final board state for the *next* turn should have '.' instead of 'R'
                final_board_list = list(board_list_after_opponent_capture)
                for k in range(n):
                    if final_board_list[k] == 'R':
                        final_board_list[k] = '.'

                possible_next_boards.add("".join(final_board_list))

    return sorted(list(possible_next_boards))  # Return sorted list for consistent output


def tom_and_jerry(n, edges):

    @lru_cache(maxsize=(n*n)//2)
    def recurse(tom, jerry, turn):
        if tom == jerry:  # Tom wins
            return False
        if jerry < tom:  # Jerry wins
            return True
        for u in edges[turn]:  # Otherwise examine all possible moves
            if turn == tom and u > tom and not recurse(u, jerry, jerry):
                return False
            elif turn == jerry and u < jerry and recurse(tom, u, tom):
                return True
        return turn == tom

    return recurse(0, n, 0)


def cubes_on_trailer(xy, xz, yz):
    xs, ys, zs = len(xy), len(yz), len(xz[0])
    exp_x = [sum(1 for z in range(zs) if xz[x][z]) for x in range(xs)]
    exp_y = [sum(1 for z in range(zs) if yz[y][z]) for y in range(ys)]
    max_x = [0 for _ in range(xs)]
    max_y = [0 for _ in range(ys)]
    possible = set()

    def recurse(x, y, z, total, slack):
        # Check that previous row fulfills its height requirements
        if x == 0 and y > 0 and max_y[y - 1] != exp_y[y - 1]:
            return
        # If entire grid completed, check if xz constraints are properly filled
        if y == ys:
            if max_x == exp_x:
                for s in range(slack + 1):
                    possible.add(total + s)
            return
        # Try not putting a box at (x, y, z) if possible
        if not xy[x][y] or z > 0:
            nx, ny = (x + 1, y) if x < xs - 1 else (0, y + 1)
            recurse(nx, ny, 0, total, slack)
        # If both x and y expected heights already reached, add this to slack
        if xy[x][y] and z == 0 and max_x[x] == exp_x[x] and max_y[y] == exp_y[y]:
            nx, ny = (x + 1, y) if x < xs - 1 else (0, y + 1)
            m = min(exp_x[x], exp_y[y])
            recurse(nx, ny, 0, total + 1, slack + m - 1)
        # Otherwise try putting a box at (x, y, z) if possible
        elif z < zs and xy[x][y] and xz[x][z] and yz[y][z]:
            old_x, old_y = max_x[x], max_y[y]
            max_x[x] = max(max_x[x], z + 1)
            max_y[y] = max(max_y[y], z + 1)
            recurse(x, y, z + 1, total + 1, slack)
            max_x[x], max_y[y] = old_x, old_y

    recurse(0, 0, 0, 0, 0)
    return min(possible), max(possible)


def powertrain(n):
    total = 0
    while n > 9:
        n = str(n)
        bases, exps, n = n[0::2], n[1::2], 1
        for (b, e) in zip_longest(bases, exps, fillvalue='0'):
            n *= int(b) ** int(e)
        total += 1
    return total


def complex_base_decode(bits):
    total, power = (0, 0), (1, 0)
    for b in reversed(bits):
        if b == '1':
            total = (total[0] + power[0], total[1] + power[1])
        # Multiply power by (I - 1)
        power = (-power[0] - power[1], power[0] - power[1])
    return total


def set_splitting(n, subsets):
    in_right = [len(subset) for subset in subsets]
    in_subset = [[] for _ in range(n)]
    for i, subset in enumerate(subsets):
        for e in subset:
            in_subset[e].append(i)
    subsets = [sorted(subset, key=lambda e:(-len(in_subset[e]), e)) for subset in subsets]

    def recurse(unsatisfied, left, tabu):
        tabu_undo = []
        if len(unsatisfied) == 0:
            return True
        now = None
        for i in unsatisfied:
            if now is None or in_right[i] < in_right[now]:
                now = i
        for e in subsets[now]:
            if e not in tabu and all(in_right[j] > 1 for j in in_subset[e]):
                undo = []
                for j in in_subset[e]:
                    in_right[j] -= 1
                    if j in unsatisfied:
                        unsatisfied.remove(j)
                        undo.append(j)
                left.append(e)
                if recurse(unsatisfied, left, tabu):
                    return True
                left.pop()
                for j in in_subset[e]:
                    in_right[j] += 1
                for j in undo:
                    unsatisfied.add(j)
                tabu.add(e)
                tabu_undo.append(e)
        for e in tabu_undo:
            tabu.remove(e)
        unsatisfied.add(now)
        return False

    return recurse(set(range(len(subsets))), [], set())


def bandwidth(edges):
    n = len(edges)

    def eliminate(u, num, possible, number, undo):
        for v in edges[u]:
            if number[v] is None:
                for nn in list(possible[v]):
                    if abs(nn - num) > d:
                        possible[v].remove(nn)
                        undo.append((v, nn))
                if len(possible[v]) == 0:
                    return False
        return True

    def recurse(remain, possible, number, taken):
        if len(remain) == 0:
            return True
        remain.sort(key=lambda u:(-len(possible[u]), len(edges[u]), u))
        u = remain.pop()
        undo = []
        for num in list(possible[u]):
            if not taken[num]:
                if eliminate(u, num, possible, number, undo):
                    number[u] = num
                    taken[num] = True
                    if recurse(remain, possible, number, taken):
                        return True
                while len(undo) > 0:
                    (v, nn) = undo.pop()
                    possible[v].add(nn)
                number[u] = None
                taken[num] = False
        remain.append(u)
        return False

    for d in range(n - 1):
        remain_ = list(range(n))
        remain_.sort(key=lambda u: (len(edges[u]), u))
        possible_ = [set(range(n if i != remain_[-1] else n//2+1)) for i in range(n)]
        if recurse(remain_, possible_, [None for _ in range(n)], [False for _ in range(n)]):
            return d
    return n - 1


def manimix(expression):
    stack = []
    for c in expression:
        if c in ")]":
            m = "9" if c == ')' else "0"
            v = stack.pop()
            while v not in "[(":
                m = min(m, v) if c == ")" else max(m, v)
                v = stack.pop()
            stack.append(m)
        else:
            stack.append(c)
    return stack[0]


def accumulating_merge(items1, items2):
    n, m = len(items1), len(items2)
    total, items, pos, result, c = [0, 0], [items1, items2], [0, 0], [], 0
    while len(result) < n + m:
        if pos[c] == len(items[c]) or (pos[1-c] < len(items[1-c]) and total[c] > total[1-c]):
            c = 1-c
        e = items[c][pos[c]]
        result.append(e)
        total[c] += e
        pos[c] += 1
    return result


def string_stretching(text):
    n, first, found = len(text), text[0], []

    def recurse(pattern, stack, i, d, owe):
        nonlocal found
        if i == n:
            if len(pattern) == d and len(stack) == 0:
                found.append(pattern)
            return
        if owe > n - i:
            return

        # Try starting a new word from the current position.
        if text[i] == first:
            stack.append(first)
            recurse(first if pattern == "" else pattern, stack, i + 1, d, owe + (d - 1))
            stack.pop()

        # Extract the current word from the stack.
        curr = stack.pop() if len(stack) > 0 else ""
        new_curr = curr + text[i]

        # Try extending the current word, extending also the pattern if necessary.
        can_extend_word = len(curr) < len(pattern) and pattern.startswith(new_curr)
        can_extend_pattern = len(curr) == len(pattern) < d and (len(pattern) < d - 1 or text[i] == text[-1])
        new_pattern = pattern if can_extend_word else new_curr
        if can_extend_word or can_extend_pattern:
            if len(new_curr) < d:
                stack.append(new_curr)
            if new_pattern not in found:
                recurse(new_pattern, stack, i + 1, d, owe - 1)
            if len(new_curr) < d:
                stack.pop()

        # Restore the current word to the stack and return None.
        if curr != "":
            stack.append(curr)
        return None

    # Iterative deepening search for pattern lengths.
    for d in range(1, n//2 + 1):
        if n % d == 0:
            recurse("", [], 0, d, 0)
            if len(found) > 0:
                return sorted(found)[0]
    return text


def conway_coin_race(a, b):
    def lead(x, y):
        return int("".join(str(bit) for bit in [int(y.startswith(x[i:])) for i in range(len(x))]), 2)

    a_term = lead(a, a) - lead(a, b)
    b_term = lead(b, b) - lead(b, a)
    return Fraction(b_term, a_term + b_term)


def baker_norine_dollar_game(edges, balance):
    balance = tuple(balance)
    n, seen, frontier = len(edges), set(), [balance]
    while len(frontier) > 0:
        curr = frontier.pop()
        seen.add(curr)
        succ = list(curr)
        for u in range(n):
            if curr[u] >= len(edges[u]):
                succ[u] -= len(edges[u])
                for v in edges[u]:
                    succ[v] += 1
                if all(c > 0 for c in succ):
                    return True
                succ_t = tuple(succ)
                if succ_t not in seen:
                    frontier.append(succ_t)
                    seen.add(succ_t)
                succ[u] += len(edges[u])
                for v in edges[u]:
                    succ[v] -= 1
    return False


def vertex_cover(edges):
    n = len(edges)
    best = n
    order = list(range(n))
    order.sort(key=lambda u: (-len(edges[u]), u))

    def recurse(d, taken):
        nonlocal best
        if len(taken) >= best:
            return
        while d < n and order[d] in taken:
            d += 1
        if d == n:
            best = min(best, len(taken))
            return
        u = order[d]
        # Try taking in node u, provided that it has any neighbour not already taken in.
        if any(v not in taken for v in edges[u]):
            taken.add(u)
            recurse(d + 1, taken)
            taken.remove(u)
        # Try taking in all neighbours of u, but not take in u itself.
        undo_list = []
        for v in edges[u]:
            if v not in taken:
                taken.add(v)
                undo_list.append(v)
        recurse(d + 1, taken)
        for v in undo_list:
            taken.remove(v)

    # Start by taking neighbour of each singleton vertex into the set.
    taken = set()
    for u in range(n):
        if u not in taken and len(edges[u]) == 1:
            v = edges[u][0]
            taken.add(v)
    # Do the recursive backtrack to select the rest.
    recurse(0, taken)
    return best


def recaman(n):
    global __prev_recaman, __lowest_unseen_rec
    if __prev_recaman > n:
        an = __prev_recaman - n
        if an < __lowest_unseen_rec or an in __recaman_seen:
            an = __prev_recaman + n
    else:
        an = __prev_recaman + n
    __prev_recaman = an
    if an >= __lowest_unseen_rec:
        __recaman_seen.add(an)
        while __lowest_unseen_rec in __recaman_seen:
            __recaman_seen.remove(__lowest_unseen_rec)
            __lowest_unseen_rec += 1
    return an


def is_caterpillar(edges):
    n = len(edges)

    # First verify that the entire graph is connected.
    found, frontier = set(), [0]
    while len(frontier) > 0:
        u = frontier.pop()
        found.add(u)
        for v in edges[u]:
            if v not in found:
                frontier.append(v)
    # If not connected, then also not a caterpillar.
    if len(found) != n:
        return False

    # Next, remove leaves.
    remain = set(range(n))
    for u in [u for u in range(n) if len(edges[u]) == 1]:
        remain.remove(u)
        v = edges[u][0]
        edges[v].remove(u)

    # Check if whatever remains after removing leaves is a path graph.
    if len(remain) < 2:
        return True  # Trivially a path graph.
    terminals = 0
    for u in remain:
        if len(edges[u]) > 2:
            return False
        if len(edges[u]) == 1:
            terminals += 1
    return terminals == 2


def sneaking(n, start, goal, knights):
    knights = set(knights)

    def update_threats(x, y, d):
        for (dx, dy) in __knight_moves:
            nx, ny = x + dx, y + dy
            if 0 <= nx < n and 0 <= ny < n:
                covers[nx][ny] += d

    covers = [[0 for _ in range(n)] for _ in range(n)]
    for (x, y) in knights:
        update_threats(x, y, +1)

    def recurse(start_, goal_, try_knight):
        seen = set()
        frontier = [start_]
        # See if we can sneak to goal past all the sleeping knights.
        while len(frontier) > 0:
            kx, ky = frontier.pop()
            seen.add((kx, ky))
            for (dx, dy) in __king_moves:
                nx, ny = kx + dx, ky + dy
                if 0 <= nx < n and 0 <= ny < n and covers[nx][ny] < 1 and (nx, ny) not in seen:
                    if (nx, ny) == goal_:
                        return True
                    frontier.append((nx, ny))
        # If not, see if we can first capture some knight and solve the problem that way.
        if try_knight:
            knight_list = list(knights)
            knight_list.sort(key=lambda k: ((k[0] - goal_[0], k[1] - goal_[1]) not in __knight_moves, k))
            for (kx, ky) in knight_list:
                if covers[kx][ky] < 1 and (kx, ky) in seen:
                    knights.remove((kx, ky))
                    update_threats(kx, ky, -1)
                    if recurse((kx, ky), goal, True):
                        return True
                    update_threats(kx, ky, +1)
                    knights.add((kx, ky))
        return False

    return recurse(start, goal, True)


def first_fit_bin_packing(items, capacity):
    bins = []
    for e in items:
        for (i, b) in enumerate(bins):
            if b + e <= capacity:
                bins[i] += e
                break
        else:
            bins.append(e)
    return bins


def word_bin_packing(words):
    n = len(words)
    best = n + 1

    hits = {word : 0 for word in words}
    for (w1, w2) in combinations(words, 2):
        if any(c1 == c2 for (c1, c2) in zip(w1, w2)):
            hits[w1] += 1
            hits[w2] += 1

    words.sort(key=lambda w:(-hits[w], w))

    def recurse(d, bins):
        nonlocal best
        if len(bins) >= best:
            return
        if d == n:
            best = min(best, len(bins))
            return
        word = words[d]
        # Try out all the ways to place word in one of the compatible existing bins.
        for bin_ in bins:
            if not any(any(c1 == c2 for (c1, c2) in zip(word, word2)) for word2 in bin_):
                bin_.append(word)
                recurse(d + 1, bins)
                bin_.remove(word)
        # Try starting a new bin with the current word.
        bins.append([word])
        recurse(d + 1, bins)
        bins.pop()

    recurse(0, [])
    return best


def independent_dominating_set(edges):
    n = len(edges)
    best = n
    order = list(range(n))
    order.sort(key=lambda u: (-len(edges[u]), u))

    def recurse(d, covered, taken):
        nonlocal best
        if len(taken) >= best:
            return
        while d < n and order[d] in covered:
            d += 1
        if d == n:
            if len(covered) == n and len(taken) < best:
                best = len(taken)
            return
        u, covered_now = order[d], []
        taken.append(u)
        covered.add(u)
        for v in edges[u]:
            if v not in covered:
                covered.add(v)
                covered_now.append(v)
        recurse(d + 1, covered, taken)
        for v in covered_now:
            covered.remove(v)
        covered.remove(u)
        taken.pop()
        recurse(d + 1, covered, taken)

    recurse(0, set(), [])
    return best


def spiral_matrix(n, row, col):
    start = 0
    while True:
        if row == 0:  # Top row
            return start + col
        if col == n - 1:  # Right column
            return start + n - 1 + row
        if row == n - 1:  # Bottom row
            return start + 3 * (n - 1) - col
        if col == 0:  # Left column
            return start + 4 * (n - 1) - row
        start += 4 * (n - 1)
        n, row, col = n - 2, row - 1, col - 1


def word_positions(sentence, word):
    return [i for (i, w) in enumerate(sentence.split()) if w == word]


def unity_partition(n):

    def rec(nn, k, total, so_far):
        if nn == 0:
            return so_far if total == __zero else None
        if total <= __zero:
            return None
        k = max(k, total.denominator // total.numerator)
        while k <= nn:
            so_far.append(k)
            if rec(nn - k, k + 1, total - Fraction(1, k), so_far):
                return so_far
            so_far.pop()
            k = k + 1 if 2 * k < nn or k == nn else nn
        return None

    result = rec(n, 2, __one, [])
    assert sum(Fraction(1, m) for m in result) == __one
    return result


def jai_alai(n, results):
    scores, king, queue = [0 for _ in range(n)], 0, Queue()
    for i in range(1, n):
        queue.put(i)
    for result in results:
        challenger = queue.get()
        if result == 'L':
            king, challenger = challenger, king
        scores[king] += 1
        queue.put(challenger)  # Back to the end of the line you go
    return scores


def tic_tac(board, player, probs):
    oppo = 'X' if player == 'O' else 'O'
    winner = None
    for trip in (board[0],
                 board[1],
                 board[2],
                 [board[0][0], board[1][0], board[2][0]],
                 [board[0][1], board[1][1], board[2][1]],
                 [board[0][2], board[1][2], board[2][2]],
                 [board[0][0], board[1][1], board[2][2]],
                 [board[2][0], board[1][1], board[0][2]],
                 ):
        if trip == [player, player, player]:
            return __one
        if trip == [oppo, oppo, oppo]:
            winner = oppo
    if winner == oppo:
        return __zero
    best = __zero
    for row in range(3):
        for col in range(3):
            if board[row][col] == '.':
                board[row][col] = player
                succ = probs[row][col] * (1 - tic_tac(board, oppo, probs))
                board[row][col] = oppo
                fail = (1 - probs[row][col]) * (1 - tic_tac(board, oppo, probs))
                board[row][col] = '.'
                best = max(best, succ + fail)
    return best


def lowest_fraction_between(first, second):
    a, b, c, d = first.numerator, first.denominator, second.numerator, second.denominator
    f = 1
    while True:
        w1 = (a * f) // b
        w2 = (c * f) // d
        if w1 < w2:
            return Fraction(w1 + 1, f)
        f += 1


def lamp_pairs(lamps):
    lamps = [b == '1' for b in lamps]
    count_, i, n = 0, 0, len(lamps)
    while i < n:
        if not lamps[i]:
            if i < n - 1 and not lamps[i + 1]:
                i += 2
                count_ += 1
            else:
                j = i + 1
                while j < n - 1 and lamps[j] != lamps[j + 1]:
                    j += 1
                if j >= n - 1:
                    return None
                count_ += (j - i) + 1
                lamps[j + 1] = not lamps[j + 1]
                i += 1
        else:
            i += 1
    return count_


def count_friday_13s(start, end):
    count_, day, week = 0, timedelta(days=1), timedelta(days=7)
    while start.isoweekday() != 5:
        start += day
    while start <= end:
        if start.day == 13:
            count_ += 1
        start += week
    return count_


def __twos_and_threes(n):
    if n == 0:
        return []
    elif n == 1:
        return [(0, 0)]
    elif n % 2 == 0:
        return [(a+1, b) for (a, b) in __twos_and_threes(n // 2)]
    else:
        k, p = 1, 3
        while p <= n:
            k, p = k + 1, p * 3
        p, k = p // 3, k-1
        return [(0, k)] + [(a+1, b) for (a, b) in __twos_and_threes((n - p) // 2)]


def twos_and_threes(n):
    return sorted(__twos_and_threes(n), key=lambda x: 2**x[0] + 3**x[1], reverse=True)


def infected_cells(infected):
    stack, infected = infected, set(infected)
    dirs = [(0, 1), (1, 0), (0, -1), (-1, 0)]
    while len(stack) > 0:
        (x, y) = stack.pop()
        for (dx, dy) in dirs:
            nx, ny = x + dx, y + dy
            if (nx, ny) not in infected:
                neighbours = 0
                for (ddx, ddy) in dirs:
                    if (nx + ddx, ny + ddy) in infected:
                        neighbours += 1
                if neighbours > 1:
                    stack.append((nx, ny))
                    infected.add((nx, ny))
    return len(infected)


def knight_jam(knights, player):
    def moves(x, y, p):
        result = []
        for d in [-1, 1]:
            nx_, ny_ = (x - 2, y + d) if p == 0 else (x + d, y - 2)
            if nx_ >= 0 and ny_ >= 0 and (nx_, ny_) not in knights:
                result.append((nx_, ny_))
        return result

    pieces = []
    for (x, y) in knights:
        for_hero = len(moves(x, y, player))
        if for_hero > 0:
            for_villain = len(moves(x, y, 1 - player))
            pieces.append((-for_villain, x, y))
    pieces.sort()

    for (_, x, y) in pieces:
        for (nx, ny) in moves(x, y, player):
            knights.remove((x, y))
            knights.add((nx, ny))
            winning_move = not knight_jam(knights, 1 - player)
            knights.remove((nx, ny))
            knights.add((x, y))
            if winning_move:
                return True
    return False


@lru_cache(maxsize=60000)
def __can_reach(n, k):
    # Too far from the origin to be reachable.
    if 2*n > k * (k + 1):
        return False
    # No more skips left, must be at the origin.
    if k == 0:
        return n == 0
    # Two possibilities for previous value from which we come to n.
    return __can_reach(abs(n - k), k - 1) or (2*(n+k) > (k - 1) * k and __can_reach(abs(n + k), k - 1))


def arithmetic_skip(n):
    k = 0
    while True:
        if __can_reach(abs(n), k):
            return k
        k += 1


def trip_flip(switches):
    n = len(switches)

    def rec(last):
        best = 0
        for i in range(max(0, last-2), n-2):
            if switches[i] != switches[i + 1] and switches[i + 1] != switches[i + 2] and switches[i + 2] != switches[i]:
                buffer = switches[i:i + 3]
                switches[i] = switches[i + 1] = switches[i + 2] = 6 - sum(buffer)
                best = max(best, 1 + rec(i))
                switches[i], switches[i + 1], switches[i + 2] = buffer[0], buffer[1], buffer[2]
        return best

    return rec(2)


def square_lamps(n, flips):
    rows = [0 for _ in range(n+1)]
    cols = [0 for _ in range(n+1)]
    for flip in flips:
        if flip < 0:
            cols[-flip] = 1 - cols[-flip]
        else:
            rows[flip] = 1 - rows[flip]
    row_on = sum(rows)
    col_on = sum(cols)
    return row_on * (n - col_on) + col_on * (n - row_on)


def lychrel(n, giveup):
    total = 0
    n = str(n)
    rn = n[::-1]
    while n != rn and giveup > 0:
        total += 1
        giveup -= 1
        n = str(int(n) + int(rn))
        rn = n[::-1]
    return total if giveup > 0 else None


def nfa(rules, text):
    state = { 0 }
    for c in text:
        next_state = set()
        for curr in state:
            for succ in rules[(curr, c)]:
                next_state.add(succ)
        state = next_state
    return sorted(state)


def dfa(rules, text):
    state = 0
    for c in text:
        state = rules[(state, c)]
    return state


def condorcet_election(ballots):
    n = len(ballots[0])
    beats = [[0 for _ in range(n)] for _ in range(n)]
    for ballot in ballots:
        for (i, c) in enumerate(ballot):
            for j in range(i+1, n):
                beats[c][ballot[j]] += 1
    matchpoints = [0 for _ in range(n)]
    for c1 in range(n-1):
        for c2 in range(c1+1, n):
            if beats[c1][c2] >= beats[c2][c1]:
                matchpoints[c1] += 1
            else:
                matchpoints[c2] += 1
    assert sum(matchpoints) == (n*(n-1))//2
    winner = 0
    for c in range(1, n):
        if matchpoints[c] > matchpoints[winner]:
            winner = c
    return winner


def repeating_decimal(a, b):
    digits, seen = [], dict()
    while True:
        if a == 0:
            return digits[0] + "." + "".join(digits[1:]), "0"
        if seen.get(a, 0) > 0:
            initial = digits[:seen[a]]
            return initial[0] + "." + "".join(initial[1:]), "".join(digits[seen[a]:])
        seen[a] = len(digits)
        digits.append(str(a // b))
        a = 10 * (a % b)


def shapley_shubik(weight, quota):
    n = len(weight)
    left = [i - 1 if i > 0 else n for i in range(n + 1)]
    right = [i + 1 if i < n else 0 for i in range(n + 1)]
    power = [0 for _ in range(n)]

    def rec(remain, m, prev):
        if remain <= 0:
            power[prev] += __fact(m)
        else:
            i = right[n]
            while i != n:
                right[left[i]] = right[i] # Joe, meet Moe
                left[right[i]] = left[i]  # Moe, meet Joe
                rec(remain - weight[i], m - 1, i)
                left[right[i]] = right[left[i]] = i  # Sorry for butting back in
                i = right[i]

    rec(quota, n, -1)
    return power


def pair_swaps(perm):
    n, total = len(perm), 0
    for i in range(n):
        e = perm[i]
        while e != i:
            perm[e], perm[i] = perm[i], perm[e]
            e = perm[i]
            total += 1
    return total


def pair_sums(n, sums):
    remain, undo_stack = dict(), []
    for s in sums:
        remain[s] = remain.get(s, 0) + 1

    def update(i, nums):
        undo_stack.append("XXX")
        for j in range(i+1, n):
            s = nums[i] + nums[j]
            if remain.get(s, 0) > 0:
                undo_stack.append(s)
                remain[s] -= 1
            else:
                unroll()
                return False
        return True

    def unroll():
        while (s := undo_stack.pop()) != "XXX":
            remain[s] += 1

    def rec(i, nums):
        if i == 0:
            return True
        for e in range(nums[i]-1, i-1, -1):
            nums[i-1] = e
            if update(i-1, nums):
                if rec(i-1, nums):
                    return True
                else:
                    unroll()
        return False

    nums = [0 for _ in range(n)]
    for last in range(sums[-1] - (n-1), n, -1):
        nums[n-1] = last
        nums[n-2] = sums[-1] - last
        assert update(n-2, nums)
        nums[n-3] = sums[-2] - last
        if nums[n-3] >= nums[n-2]:
            unroll()
            continue
        if update(n-3, nums):
            if rec(n-3, nums):
                return nums
            unroll()
        unroll()
    assert False


def count_triangles(sides):
    n, total = len(sides), 0
    for i in range(2, n):
        j = i-1
        while j >= 1 and sides[j] + sides[j] > sides[i]:
            k = j-1
            while k >= 0 and sides[k] + sides[j] > sides[i]:
                total += 1
                k -= 1
            j -= 1
    return total


def place_disks(points, r):
    n, best, overlap = len(points), 0, {p: [] for p in points}
    for ((x1, y1), (x2, y2)) in combinations(points, 2):
        if (x2-x1)**2 + (y2-y1)**2 <= 4*r*r:
            overlap[(x1, y1)].append((x2, y2))
            overlap[(x2, y2)].append((x1, y1))
    points.sort(key=lambda p:(len(overlap[p]), p))

    def rec(i, taken, remain):
        nonlocal best
        if i < n:
            p = points[i]
            # Try placing a disk on point p
            if p in remain:
                undo_stack = []
                for (x, y) in overlap[p]:
                    if (x, y) in remain:
                        undo_stack.append((x, y))
                        remain.remove((x, y))
                rec(i+1, taken + 1, remain)
                for (x, y) in undo_stack:
                    remain.add((x, y))
            # Try not placing a disk on point p
            rec(i+1, taken, remain)
        else:
            best = max(best, taken)

    rec(0, 0, set(points))
    return best


def longest_zigzag(items):
    n = len(items)
    table = [[1 for _ in range(n)] for _ in range (2)]
    for col in range(n-2, -1, -1):
        for row in range(2):
            for pos in range(col+1, n):
                if items[pos] > items[col] if row == 0 else items[pos] < items[col]:
                    table[row][col] = max(table[row][col], 1 + table[1-row][pos])
    return max(table[0][0], table[1][0])


def median_filter(items, k):
    result, center = [], k // 2
    window = [items[0] for _ in range(k-1)]
    for e in items:
        window.append(e)
        result.append(sorted(window)[center])
        window = window[1:]
    return result


def domino_pop(dominos):
    n = len(dominos)
    best = n

    def match(d1, d2):
        return d1[1] == 0 or d2[0] == 0 or d1[1] == d2[0]

    def rec(pos, stack):
        nonlocal best
        if len(stack) - (n - pos) >= best:
            return
        elif pos == n:
            best = min(best, len(stack))
        else:
            d = dominos[pos]
            # Try popping if possible
            if len(stack) > 0 and match(stack[-1], d):
                dd = stack.pop()
                rec(pos + 1, stack)
                stack.append(dd)
            # Try not popping
            stack.append(d)
            rec(pos + 1, stack)
            stack.pop()

    rec(0, [])
    return best


def self_describe(items):
    c, best = dict(), len(items)
    for e in items:
        c[e] = c.get(e, 0) + 1

    def partition(n, k, sofar):
        if n == 0:
            yield sofar[:]
        else:
            while k * (k + 1) >= 2 * n:
                sofar.append(k)
                yield from partition(n - k, min(n - k, k - 1), sofar)
                sofar.pop()
                k = k - 1

    for p in partition(len(items), len(items), []):
        best = min(best, sum(max(0, x - c.get(x, 0)) for x in p))
    return best


def arrow_walk(board, position):
    board = [(-1 if c == '<' else +1) for c in board]
    n, total = len(board), 0
    while 0 <= position < n:
        board[position], position, total = -board[position], position + board[position], total + 1
    return total


def itky_leda(board):
    n, total = len(board), 0
    curr_list = [(0, 0, n-1, n-1)]
    curr_seen = set(curr_list)
    other_list = [(n-1, n-1, 0, 0)]
    other_seen = set(other_list)

    def succ_list(x, y, d, ox, oy):
        result = []
        for (dx, dy) in [(0, d), (0, -d), (d, 0), (-d, 0)]:
            nx, ny = x+dx, y+dy
            if 0 <= nx < n and 0 <= ny < n and (nx, ny) != (ox, oy):
                result.append((nx, ny))
        return result

    while True:
        next_layer = []
        total += 1
        for (x0, y0, x1, y1) in curr_list:
            red_steps = [(x, y, x1, y1) for (x, y) in succ_list(x0, y0, board[x1][y1], x1, y1)]
            blue_steps = [(x0, y0, x, y) for (x, y) in succ_list(x1, y1, board[x0][y0], x0, y0)]
            for step in chain(red_steps, blue_steps):
                if step in other_seen:
                    return total
                if step not in curr_seen:
                    curr_seen.add(step)
                    next_layer.append(step)
        if not next_layer:
            return -1
        curr_seen, other_seen = other_seen, curr_seen
        curr_list, other_list = other_list, next_layer


def lowest_common_dominator(beta, gamma):
    s1, s2, seq = 0, 0, []
    for (e1, e2) in zip(beta, gamma):
        s1 += e1
        s2 += e2
        seq.append(max(s1, s2))
    return seq


def str_rts(text):
    pos, best = dict(), 0
    for (i, c) in enumerate(text):
        if c not in pos:
            pos[c] = [i]
        else:
            pos[c].append(i)
    for c in pos:
        for (i, j) in combinations(pos[c], 2):
            k = 0
            if i + 2*best < j:
                while i < j and text[i] == text[j]:
                    k, i, j = k+1, i+1, j-1
                best = max(k, best)
    return best


def is_string_shuffle(first, second, result):
    n1, n2 = len(first), len(second)

    @lru_cache(maxsize=n1*n2)
    def rec(i, j):
        if i == 0:
            return second[:j] == result[:j]
        elif j == 0:
            return first[:i] == result[:i]
        else:
            return (second[j-1] == result[i+j-1] and rec(i, j-1)) or (first[i-1] == result[i+j-1] and rec(i-1, j))

    return rec(n1, n2)


def count_cigarettes(n, k):
    total, butts = 0, 0
    while n > 0:
        total += n
        butts += n
        n = butts // k
        butts = butts % k
    return total


def van_der_corput(base, n):
    result, mul = 0, Fraction(1, base)
    while n > 0:
        d = n % base
        n = n // base
        result += d * mul
        mul *= Fraction(1, base)
    return result


def super_tiny_rng(seed, n, bits):
    result, x = [], seed
    for _ in range(n):
        r = 0
        for _ in range(bits):
            x = (x + (x*x | 5)) & 0xFFFFFFFF
            r = 2*r + ((x & (1 << 31)) >> 31)
        result.append(r)
    return result


def carving_egyptian(f):
    result = set()
    while f > 0:
        a, b = f.numerator, f.denominator
        f = Fraction(a-1, b)
        buffer = [b]
        while buffer:
            n = buffer.pop()
            if n in result:
                result.remove(n)
                if n % 2 == 0:
                    buffer.append(n // 2)
                else:
                    buffer.append((n+1)//2)
                    buffer.append((n*(n+1))//2)
            else:
                result.add(n)
    return sorted(result)


def greedy_egyptian(f):
    result = []
    while True:
        a, b = f.numerator, f.denominator
        if a == 1:
            result.append(b)
            return result
        n = (b // a) + 1
        result.append(n)
        f = f - Fraction(1, n)


def minimal_egyptian(f, k, n=1):
    if k == 0:
        return False
    a, b = f.numerator, f.denominator
    if a == 1 and b >= n:
        return True
    n = max(n, (b // a) + 1)
    while k * Fraction(1, n) >= f:
        ff = f - Fraction(1, n)
        if minimal_egyptian(ff, k - 1, n + 1):
            return True
        n += 1
    return False


def __normalize(pins):
    prev, result = -1, []
    for p in sorted(pins, reverse=True):
        if p == 0:
            break
        if p != prev:
            result.append(p)
            prev = p
        else:
            result.pop()
            prev = -1
    return result


def kayles(pins, depth=0):
    if len(pins) == 0:
        return False
    if len(pins) == 1:
        return True
    for (i, p) in enumerate(pins):
        # Knock out one pin from end.
        pins[i] = p-1
        if not kayles(__normalize(pins), depth + 1):
            return True
        pins[i] = p
        # Knock out two pins from end.
        if p > 1:
            pins[i] = p-2
            if not kayles(__normalize(pins), depth + 1):
                return True
            pins[i] = p
        # Knock out one or two internal pins.
        for pos in range(1, (p+1)//2):
            # One internal pin.
            pins[i] = pos
            pins.append(p-1-pos)
            if not kayles(__normalize(pins), depth + 1):
                return True
            pins.pop()
            pins[i] = p
            # Two internal pins.
            if pos < p-2:
                pins[i] = pos
                pins.append(p-2-pos)
                if not kayles(__normalize(pins), depth + 1):
                    return True
                pins.pop()
                pins[i] = p
    return False


def reversenacci(i, n):
    m = n - 1
    while 2*m > n:
        a, b = m, n
        for j in range(i-1):
            c = b - a
            if c < 1 or c > a:
                break
            a, b = c, a
        else:
            return True
        m = m - 1
    return False


def carryless_addition(a, b):
    total, p = 0, 1
    while a > 0 or b > 0:
        c = ((a % 10) + (b % 10)) % 10
        total += c * p
        p *= 10
        a, b = a // 10, b // 10
    return total


def carryless_single_digit_multiply(a, b):
    total, p = 0, 1
    while a > 0:
        a, c = a // 10, a % 10
        total += p * ((b * c) % 10)
        p *= 10
    return total


def carryless_multiplication(a, b):
    total, p = 0, 1
    a, b = max(a, b), min(a, b)
    while b > 0:
        row = carryless_single_digit_multiply(a, b % 10) * p
        total = carryless_addition(total, row)
        b = b // 10
        p *= 10
    return total


def game_with_multiset(queries):
    natural = [0 for _ in range(3)]
    result = []
    for op, val in queries:
        while val >= len(natural):
            natural.append(0)
        if op == 'A':
            natural[val] += 1
        elif op == 'G':
            need = 0
            bits = (bin(val)[2:])
            n = len(bits) - 1
            for (pos, b) in enumerate(bits):
                need += int(b)
                need = max(0, need - natural[n - pos]) * 2
            result.append(need == 0)
    return result


def nice_sequence(items, start):
    step = {n:[] for n in items}
    for (a, b) in combinations(items, 2):
        if a % b == 0 or b % a == 0:
            if b != start:
                step[a].append(b)
            if a != start:
                step[b].append(a)

    best = []

    def recurse(so_far, taken):
        nonlocal best
        if len(so_far) > len(best):
            best = so_far[:]
        for n in [n for n in step[so_far[-1]] if n not in taken]:
            so_far.append(n)
            taken.add(n)
            recurse(so_far, taken)
            taken.remove(n)
            so_far.pop()

    recurse([start], set())
    return len(best)


def prize_strings(n, late_limit, absent_limit):

    @lru_cache(maxsize=n*4)
    def recurse(nn, late_remain, absent_consecutive):
        if late_remain == 0 or absent_consecutive == 0:
            return 0
        if nn == 0:
            return 1
        today_on_time = recurse(nn - 1, late_remain, absent_limit)
        today_late = recurse(nn - 1, late_remain - 1, absent_limit)
        today_absent = recurse(nn - 1, late_remain, absent_consecutive - 1)
        return today_on_time + today_late + today_absent

    return recurse(n, late_limit, absent_limit)


def goodstein(n, k):
    g, i = n, 2
    while i <= k and g > 0:
        coeff, gg = [], g
        while gg > 0:
            coeff.append(gg % i)
            gg = gg // i
        gg, p = 0, 1
        for c in coeff:
            gg = gg + c * p
            p = p * (i + 1)
        g = gg - 1
        i += 1
    return g


def max_product(digits, n, m):
    best = 0

    def recurse(i, first, second):
        nonlocal best
        if len(first) == n:
            best = max(best, int(first) * int(second + digits[i:]))
        elif len(second) == m:
            best = max(best, int(first + digits[i:]) * int(second))
        else:
            k = 1
            while i + k < len(digits) and digits[i + k] == digits[i]:
                k += 1
            for j in range(k + 1):
                if len(first) + j <= n and len(second) + (k-j) <= m:
                    recurse(i + k, first + digits[i:i+j], second + digits[i+j:i+k])

    recurse(0, "", "")
    return best


def count_unicolour_rectangles(grid):
    n, m = len(grid), len(grid[0])
    result = 0
    for x in range(n-1):
        for y in range(m-1):
            colour = grid[x][y]
            for hx in range(1, n-x):
                if colour == grid[x+hx][y]:
                    for hy in range(1, m-y):
                        if colour == grid[x][y+hy] == grid[x+hx][y+hy]:
                            result += 1
    return result


def markov_distance(n1, n2):
    def predecessor(n):
        (x, y, z) = n
        neighbours = [
            tuple(sorted([x, y, 3 * x * y - z])),
            tuple(sorted([x, z, 3 * x * z - y])),
            tuple(sorted([y, z, 3 * y * z - x])),
        ]
        return sorted(neighbours, key=lambda t:t[2])[0]
    result = 0
    while n1 != n2:
        result += 1
        if n1[2] < n2[2]:
            n2 = predecessor(n2)
        else:
            n1 = predecessor(n1)
    return result


def gijswijt(n):
    global __gijswijt
    while n >= len(__gijswijt):
        k, best = 1, 1
        while best < 4 and (best+1)*k <= len(__gijswijt):
            for j in range(2, 5):
                failed = False
                if j*k <= len(__gijswijt):
                    i = 0
                    while i < k:
                        if __gijswijt[-k + i] != __gijswijt[-j*k + i]:
                            failed = True
                            break
                        i += 1
                    else:
                        best = max(best, j)
                else:
                    break
                if failed:
                    break
            k += 1
        __gijswijt.append(best)
    return __gijswijt[n]


def parking_lot_permutation(preferred_spot):
    n = len(preferred_spot)
    parking = [None for _ in range(n)]
    for (i, p) in enumerate(preferred_spot):
        while parking[p] is not None:
            p = (p + 1) % n
        parking[p] = i
    return parking


def tower_of_babel(blocks):
    blocks = [tuple(sorted(block, reverse=True)) for block in blocks]
    best, m = 0, max(block[0] for block in blocks) + 1

    def rec(a, b, blocks_, h):
        nonlocal best
        best = max(best, h)
        for i, (x, y, z) in enumerate(blocks_):
            new_blocks = blocks_[:i] + blocks_[i + 1:]
            if x < a and y < b:
                rec(x, y, new_blocks, h + z)
            if x < a and z < b:
                rec(x, z, new_blocks, h + y)
            if y < a and z < b:
                rec(y, z, new_blocks, h + x)

    rec(m, m, blocks, 0)
    return best


def vector_add_reach(start, goal, vectors, giveup):
    curr_set, other_set = {start}, {goal}
    curr_list, other_list = [start], [goal]
    nectors = list(tuple(-d for d in vector) for vector in vectors)
    steps = 0
    while True:
        steps += 1
        if steps > giveup:
            return None
        next_list = []
        for curr_state in curr_list:
            for vector in vectors:
                next_state = tuple(x + y for (x, y) in zip(curr_state, vector))
                if all(c >= 0 for c in next_state):
                    if next_state in other_set:
                        return steps
                    if next_state not in curr_set:
                        next_list.append(next_state)
                        curr_set.add(next_state)
        other_list, curr_list, other_set, curr_set, vectors, nectors = next_list, other_list, curr_set, other_set, nectors, vectors


def mmu_lru(n, pages):
    slots, lru = [None for _ in range(n)], [-1 for _ in range(n)]
    total = 0
    for (t, p) in enumerate(pages):
        min_idx = -1
        for (idx, f) in enumerate(slots):
            if f == p:
                min_idx = idx
                break
        if min_idx == -1:
            total += 1
            min_lru, min_idx = t, 0
            for (idx, (f, l)) in enumerate(zip(slots, lru)):
                if f is None or l < lru[min_idx]:
                    min_idx, min_lru = idx, l
            slots[min_idx] = p
        lru[min_idx] = t
    return total


def mmu_optimal(n, pages):
    total, m = 0, len(pages)
    slots = [None for _ in range(n)]
    uses = {p:[m] for p in pages}
    for (t, p) in enumerate(reversed(pages)):
        uses[p].append(m - (t+1))
    for (t, p) in enumerate(pages):
        if p not in slots:
            total += 1
            max_idx, max_t = -1, 0
            for (idx, f) in enumerate(slots):
                if f is None:
                    max_idx, max_t = idx, m
                else:
                    if uses[f][-1] > max_t:
                        max_idx, max_t = idx, uses[f][-1]
            slots[max_idx] = p
        uses[p].pop()
    return total


def count_distinct_substrings(text):
    result, current, n = 1, {text}, len(text)
    if n == 0:
        return 0
    while n > 1:
        next_ = set()
        for pat in current:
            next_.add(pat[1:])
            next_.add(pat[:-1])
        result += len(next_)
        current = next_
        n -= 1
    return result


def measure_balsam(flasks, goal):
    steps, n = 0, len(flasks)
    init = [0 for _ in range(n)]
    init[0] = flasks[0]
    seen, queue = {tuple(init)}, [init]
    while len(queue) > 0:
        targets = []
        steps += 1
        for conf in queue:
            for i in range(n):
                if conf[i] > 0:
                    for j in range(n):
                        if i != j and conf[j] < flasks[j]:
                            pour = min(conf[i], flasks[j] - conf[j])
                            next_conf = conf[:]
                            next_conf[i] -= pour
                            next_conf[j] += pour
                            if goal in next_conf:
                                return steps
                            next_conf_t = tuple(next_conf)
                            if next_conf_t not in seen:
                                seen.add(next_conf_t)
                                targets.append(next_conf)
        queue = targets
    return None


def digit_partition(digits, n):

    def recurse(i, m):
        if i == 0:
            return m == 0
        if m < 0:
            return False
        ml = len(str(m))
        if i < ml:
            return False
        for k in range(1, ml+1):
            if recurse(i - k, m - int(digits[i - k:i])):
                return True
        return False

    return recurse(len(digits), n)


def tr(text, ch_from, ch_to):
    sub = {c1: c2 for (c1, c2) in zip(ch_from, ch_to)}
    return "".join(sub.get(c, c) for c in text)


def cube_tower(cubes):
    n = len(cubes)

    @lru_cache(maxsize=n*6)
    def rec(i, c):
        score = 0
        if i >= 0:
            # Take cube i to the tower, if you can
            for j in range(6):
                if c is None or cubes[i][j] == c:
                    score = max(score, 1 + rec(i-1, cubes[i][(j+3) % 6]))
            # Leave out the cube i from the tower
            score = max(score, rec(i-1, c))
        return score

    return rec(n-1, None)


def des_chiffres(board, goal):
    n = len(board)

    def rec(items_, limit_):
        if limit_ == 0:
            return False
        nn = len(items_)
        prev = 0
        for i in range(nn-1):
            e1 = items_[i]
            if e1 != prev:
                for j in range(i+1, nn):
                    e2 = items_[j]
                    es = [e for e in [e1+e2, e1*e2, e2-e1] if e > 0]
                    if e2 % e1 == 0:
                        es.append(e2 // e1)
                    if goal in es:
                        return True
                    new_items = items_[:i] + items_[i + 1:j] + items_[j + 1:]
                    for e in es:
                        if rec(sorted(new_items + [e]), limit_ - 1):
                            return True
            prev = e1

    for limit in range(1, n):
        if rec(sorted(board), limit):
            return limit
    return None


def squares_total_area(points):
    cover = []
    for (x, y) in points:
        s = min(x, y)
        for (xx, yy, ss) in cover:
            if xx <= x and yy <= y:
                s = min(s, max(x-xx, y-yy))
            elif xx <= x and yy < y + ss:
                s = min(s, x-xx)
            elif x < xx < x + ss and y <= yy < y + ss:
                s = 0
            elif x < xx < x + ss and yy < y:
                s = min(s, y-yy)
            if s < 1:
                break
        else:
            cover.append((x, y, s))
    return sum(s*s for (_, _, s) in cover)


def fewest_boxes(items, weight_limit):
    box_count, lo, hi = 0, 0, len(items)-1
    while lo <= hi:
        box_count += 1
        if lo < hi and items[lo] + items[hi] <= weight_limit:
            lo += 1
        hi -= 1
    return box_count


def bridge_score(strain, level, vul, doubled, made):
    mul = {'X': 2, 'XX': 4}.get(doubled, 1)
    score, bonus = 0, 0

    # Add up the values of individual tricks.
    for trick in range(1, made+1):
        # Raw points for this trick.
        if strain == 'clubs' or strain == 'diamonds':
            pts = 20
        elif strain == 'hearts' or strain == 'spades':
            pts = 30
        else:
            pts = 40 if trick == 1 else 30
        # Score from the raw points.
        if trick <= level:  # Part of contract
            score += mul * pts
        elif mul == 1:  # Undoubled overtrick
            bonus += mul * pts
        elif mul == 2:  # Doubled overtrick
            bonus += 200 if vul else 100
        else:  # Redoubled overtrick
            bonus += 400 if vul else 200
    if score >= 100:  # Game bonus
        bonus += 500 if vul else 300
    else:  # Partscore bonus
        bonus += 50
    if level == 6:  # Small slam bonus
        bonus += 750 if vul else 500
    if level == 7:  # Grand slam bonus
        bonus += 1500 if vul else 1000
    score += bonus
    if mul == 2:  # Insult bonus for making a (re)doubled contract
        score += 50
    elif mul == 4:
        score += 100
    return score


def trip_plan(motels, daily_drive):
    # Prepend a zero to the motels list to serve as sta.
    motels = [0] + motels
    # Initialize the cost and move tables.
    n = len(motels)
    cost = [None for _ in range(n)]   # Optimal solution cost starting from each motel.
    move = [None for _ in range(n)]   # The optimal first move starting from each motel.

    # Fill in the optimal cost and move tables.
    cost[n-1] = 0  # Base case of recursion.
    for i in range(n-2, -1, -1):
        for j in range(i+1, n):
            total_cost = (daily_drive - (motels[j] - motels[i])) ** 2 + cost[j]
            if cost[i] is None or cost[i] > total_cost:
                cost[i] = total_cost
                move[i] = j

    # Reconstruct the optimal solution from the move table.
    result, curr = [], 0
    while curr < n-1:
        curr = move[curr]
        result.append(motels[curr])
    return result


def __extract_number(text, pos):
    n = 0
    while pos < len(text) and text[pos].isdigit():
        n = 10 * n + int(text[pos])
        pos += 1
    return n, pos


def tog_comparison(first, second):
    pos = 0
    while pos < len(first) and pos < len(second):
        c0, c1 = first[pos], second[pos]
        if c0.isdigit() and c1.isdigit():
            n0, _ = __extract_number(first, pos)
            n1, pos = __extract_number(second, pos)
        else:
            n0, n1 = ord(c0), ord(c1)
            pos += 1
        if n0 < n1:
            return -1
        elif n1 < n0:
            return +1
    if pos < len(first):
        return +1
    elif pos < len(second):
        return -1
    else:
        return 0


def repetition_resistant(n):
    global __rr_seq, __rr_max
    while len(__rr_seq) <= n:
        suf = __rr_seq[-__rr_max:] if __rr_max > 0 else ""
        suf0, suf1 = suf + '0', suf + '1'
        idx0, idx1 = __rr_seq.find(suf0), __rr_seq.find(suf1)
        has0 = idx0 >= 0 and idx0 + __rr_max < len(__rr_seq)
        has1 = idx1 >= 0 and idx1 + __rr_max < len(__rr_seq)
        __rr_seq += '1' if has0 and not has1 else '0'
        __rr_max += 1 if has0 and has1 else 0
    return __rr_seq[n]


def kimberling_expulsion(start, end):
    global __kim_left, __kim_right
    __kim_left, right = __kim_left, __kim_right
    result = []

    def get(idx):
        nonlocal right
        while idx >= len(__kim_left):
            __kim_left.append(right)
            right += 1
        return __kim_left[idx]

    for i in range(start, end):
        result.append(get(i))
        new_left = []
        for j in range(1, i + 1):
            new_left.append(get(i + j))
            new_left.append(get(i - j))
        __kim_left = new_left

    __kim_left, __kim_right = __kim_left, right
    return result


def hofstadter_figure_figure(n):
    global __hof_missing, __hof_idx
    while n >= len(__hof_r):
        new_r = __hof_r[-1] + __hof_s[-1]
        __hof_r.append(new_r)
        new_s = __hof_s[-1] + 1
        while new_s > __hof_r[__hof_idx]:
            __hof_idx += 1
        if new_s == __hof_r[__hof_idx]:
            new_s += 1
        __hof_s.append(new_s)
    return __hof_r[n], __hof_s[n]


def langford_violations(items):
    wrong, n = [], len(items) // 2
    seen = [None for _ in range(n + 1)]
    for i, e in enumerate(items):
        if seen[e] is None:
            seen[e] = i
        elif i - seen[e] != e + 1:
            wrong.append(e)
    return sorted(wrong)


def shotgun(n):
    k = n - 1
    while k > 0:
        kk = k + 1
        if n % kk == 0:
            n = n + kk if (n // kk) % 2 == 1 else n - kk
        k -= 1
    return n


# Cleaner solution submitted by Karel Tutsu.

def count_palindromes(text):
    n, count_ = len(text), 0
    for i in range(1, n - 1):
        # 0 - Case Odd & 1 - Case Even
        for j in [0, 1]:
            left, right = i, i + j
            while left >= 0 and right < n and text[left] == text[right]:
                if (right - left + 1) >= 3:
                    count_ += 1
                left -= 1
                right += 1
    return count_


def mu_torere_moves(board, player):
    k, moves = len(board) // 2, set()
    n = 2 * k
    board, last = board[:n], board[n]
    board_l = [p for p in board]
    for i, p in enumerate(board):
        if p == player:
            left, right = (i - 1) % n, (i + 1) % n
            # Move left
            if board_l[left] == '-':
                board_l[left], board_l[i] = board_l[i], board_l[left]
                moves.add("".join(board_l) + last)
                board_l[left], board_l[i] = board_l[i], board_l[left]
            # Move right
            if board_l[right] == '-':
                board_l[right], board_l[i] = board_l[i], board_l[right]
                moves.add("".join(board_l) + last)
                board_l[right], board_l[i] = board_l[i], board_l[right]
            # Move to center
            if last == '-' and (board_l[left] != player or board_l[right] != player):
                board_l[i] = '-'
                moves.add("".join(board_l) + player)
                board_l[i] = player
        # Move from center
        elif p == '-' and last == player:
            board_l[i] = player
            moves.add("".join(board_l) + "-")
            board_l[i] = "-"
    return sorted(moves)


def discrete_rounding(n):
    for k in range(n - 1, 1, -1):
        d = n // k
        if n > d * k:
            n = (d + 1) * k
    return n


def stern_brocot(x):
    a, b, c, d = 0, 1, 1, 0
    result = []
    while True:
        m = Fraction(a + c, b + d)
        result.append(m)
        if m == x:
            return result
        elif m < x:
            a, b = m.numerator, m.denominator
        else:
            c, d = m.numerator, m.denominator


def abacaba(n):
    k, p = 0, 1
    while n >= p - 1:
        k, p = k + 1, p * 2
    while True:
        nn = 2 * (n + 1)
        if nn == p:
            return k - 1
        elif nn > p:
            n = n - p // 2
        k, p = k - 1, p // 2


__keys = {'a': 2, 'b': 2, 'c': 2, 'd': 3, 'e': 3, 'f': 3, 'g': 4, 'h': 4, 'i': 4,
          'j': 5, 'k': 5, 'l': 5, 'm': 6, 'n': 6, 'o': 6, 'p': 7, 'q': 7, 'r': 7,
          's': 7, 't': 8, 'u': 8, 'v': 8, 'w': 9, 'x': 9, 'y': 9, 'z': 9}

__word_keys = dict()


def keypad_words(number, words):
    if not __word_keys:
        for word in words:
            code = "".join(str(__keys[c]) for c in word)
            if code in __word_keys:
                __word_keys[code].append(word)
            else:
                __word_keys[code] = [word]

    @lru_cache(maxsize=7)
    def all_keywords(number_):
        if len(number_) == 0:
            return [""]
        else:
            result = []
            for i in range(1, len(number_) + 1):
                num_prefix = number_[:i]
                for prefix in __word_keys.get(num_prefix, []):
                    for suffix in all_keywords(number_[i:]):
                        if suffix:
                            result.append(prefix + "-" + suffix)
                        else:
                            result.append(prefix)
            return result

    return sorted(set(all_keywords(number)))


def break_bad(word, elements):
    n, elements = len(word), set(elements)
    # Cost of breaking word starting from given position.
    cost = [0 for _ in range(n + 1)]
    # The optimal move to make in each position.
    move = [0 for _ in range(n + 1)]

    # Fill in the cost and move tables from end to beginning.
    for pos in range(n-1, -1, -1):
        # Try a one-letter element.
        if word[pos].title() in elements:
            cost[pos] = 1 + cost[pos + 1]
            move[pos] = 1
        else:
            cost[pos] = 2 + cost[pos + 1]
        # Try a two-letter element.
        if n - pos > 1 and word[pos:pos + 2].title() in elements and cost[pos + 2] <= cost[pos]:
            cost[pos] = cost[pos + 2]
            move[pos] = 2

    # Reconstruct the optimal solution from the cost table.
    result, pos = '', 0
    while pos < n:
        if move[pos] == 2:
            result += f"[{word[pos:pos + 2].title()}]"
            pos += 2
        elif move[pos] == 1:
            result += f"[{word[pos].title()}]"
            pos += 1
        else:
            result += word[pos]
            pos += 1
    return result


def forbidden_digit(n, d):
    if n == 0:
        return 0 if d > 0 else 1
    result = []
    while n > 0:
        dig, n = n % 9, n // 9
        result.append(str(dig if dig < d else dig + 1))
    return int("".join(reversed(result)))


def blocking_pawns(n, queens):
    best = len(queens) * len(queens)
    queens = set(queens)
    dirs = [(0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1)]

    def between(x0, y0, px, py, x1, y1, dx, dy):
        nx, ny = x0 + dx, y0 + dy
        while nx != x1 or ny != y1:
            if nx == px and ny == py:
                return True
            else:
                nx, ny = nx + dx, ny + dy
        return False

    def compute_attack_pairs():
        attack_pairs_ = set()
        for (x, y) in queens:
            for (dx, dy) in dirs:
                nx, ny = x + dx, y + dy
                while 0 <= nx < n and 0 <= ny < n:
                    if (nx, ny) in queens:
                        if (nx, ny) < (x, y):
                            attack_pairs_.add(((x, y), (nx, ny), (dx, dy)))
                        break
                    else:
                        nx, ny = nx + dx, ny + dy
        return attack_pairs_

    def place_blockers(pawns):
        nonlocal best
        if pawns >= best:
            return
        if len(attack_pairs) == 0:
            best = pawns
        else:
            (x0, y0), (x2, y2), (dx, dy) = attack_pairs.pop()
            px, py = x0 + dx, y0 + dy
            while px != x2 or py != y2:
                blocked = []
                for (xx0, yy0), (xx1, yy1), (ddx, ddy) in attack_pairs:
                    if between(xx0, yy0, px, py, xx1, yy1, ddx, ddy):
                        blocked.append(((xx0, yy0), (xx1, yy1), (ddx, ddy)))
                for pair in blocked:
                    attack_pairs.remove(pair)
                place_blockers(pawns + 1)
                for pair in blocked:
                    attack_pairs.add(pair)
                px, py = px + dx, py + dy
            attack_pairs.add(((x0, y0), (x2, y2), (dx, dy)))

    attack_pairs = compute_attack_pairs()
    place_blockers(0)
    return best


def optimal_blackjack(deck):
    n, deck = len(deck), deck + deck

    def add_card(total, soft, card):
        total += card
        if card == 11:
            soft += 1
        if total > 21 and soft:
            total -= 10
            soft -= 1
        return total, soft

    @lru_cache(maxsize=n)
    def player_move(pos):
        if pos + 3 >= n:
            return 0
        player_total, player_soft = add_card(0, 0, deck[pos])
        player_total, player_soft = add_card(player_total, player_soft, deck[pos + 1])
        dealer_start, dealer_soft = add_card(0, 0, deck[pos + 2])
        dealer_start, dealer_soft = add_card(dealer_start, dealer_soft, deck[pos + 3])
        best, player_take_pos = -n, 4
        while player_total <= 21:
            dealer_total, dealer_take_pos, soft = dealer_start, player_take_pos, dealer_soft
            while dealer_total < 17:
                dealer_total, soft = add_card(dealer_total, soft, deck[pos + dealer_take_pos])
                dealer_take_pos += 1
            score = -1 if 22 > dealer_total > player_total else (0 if dealer_total == player_total else +1)
            best = max(best, score + player_move(pos + dealer_take_pos))
            player_total, player_soft = add_card(player_total, player_soft, deck[pos + player_take_pos])
            player_take_pos += 1
        return max(best, player_move(pos + player_take_pos) - 1)

    return player_move(0)


def insertion_sort_swaps(items):
    total, n = 0, len(items)
    for i in range(1, n):
        j, item = i, items[i]
        while j > 0 and items[j - 1] > item:
            total += 1
            items[j] = items[j - 1]
            j -= 1
        items[j] = item
    return total


def stalin_sort(items):
    if not items:
        return 1
    init_prev, rounds = min(items), 0
    while True:
        proles, kulaks, prev = [], [], init_prev
        for e in items:
            if e < prev:
                kulaks.append(e)
            else:
                proles.append(e)
                prev = e
        rounds += 1
        if not kulaks:
            return rounds
        items = kulaks + proles


def smetana_interpreter(program):
    def smetana_step(env):
        pc, code = env['pc'], env['code']
        ins, *ops = code[pc].split(' ')
        if ins == 'GOTO':
            env['pc'] = pc = int(ops[0])
        elif ins == 'SWAP':
            s1, s2 = int(ops[0]), int(ops[1])
            code[s1], code[s2] = code[s2], code[s1]
            env['pc'] = pc = pc + 1
        return pc >= len(program)

    step_count = 0
    tortoise, hare = {'pc': 0, 'code': program}, {'pc': 0, 'code': program[:]}
    while True:
        step_count += 1
        if smetana_step(hare):
            return step_count
        if step_count % 2 == 0:
            smetana_step(tortoise)
            if hare == tortoise:
                return None


def card_row_game(cards):
    n = len(cards)

    @lru_cache(maxsize=n * n // 2)
    def solve(i, j):
        if i == j:
            return cards[i]
        else:
            return max(cards[i] - solve(i + 1, j), cards[j] - solve(i, j - 1))

    return solve(0, n - 1)


def has_majority(items):
    count_, curr, edge = 0, None, 0
    for e in items:
        if count_ == 0:
            curr = e
            count_ = 1
        else:
            count_ += 1 if curr == e else -1
    for e in items:
        edge += 1 if e == curr else -1
    return edge > 0


def bus_travel(schedule, goal):
    best, arrival, frontier = (24, 0), {0: (0, 0)}, {0}
    while len(frontier) > 0:
        current_city = frontier.pop()
        time = arrival[current_city]
        for (destination, leave, arrive) in schedule[current_city]:
            if leave >= time and arrive < best:
                if destination == goal:
                    best = min(best, arrive)
                elif destination not in arrival or arrival[destination] > arrive:
                    arrival[destination] = arrive
                    frontier.add(destination)
    return best


def multiplicative_persistence(n, ignore_zeros=False):
    count_ = 0
    while n > 9:
        count_ += 1
        prod = 1
        while n > 0:
            d = n % 10
            if d > 0 or not ignore_zeros:
                prod *= d
            n = n // 10
        n = prod
    return count_


def count_odd_sum_sublists(items):
    odd_count, even_count, total, count_ = 0, 1, 0, 0
    for e in items:
        total += e
        if total % 2 == 0:
            count_ += odd_count
            even_count += 1
        else:
            count_ += even_count
            odd_count += 1
    return count_


def largest_ones_square(board):

    @lru_cache()
    def solve(row, col):
        if row < 0 or col < 0 or board[row][col] == '0':
            return 0
        else:
            return 1 + min(solve(row - 1, col), solve(row - 1, col - 1), solve(row, col - 1))

    return max(solve(row, col) for (row, col) in product(range(len(board)), repeat=2))


def accumulate_dice(d, goal):
    one_d = Fraction(1, d)

    @lru_cache(maxsize=10000)
    def prob(s, k):
        if k == 0:
            return __one if s == 0 else __zero
        else:
            total = __zero if s < goal else prob(s, k - 1)
            for sp in range(max(0, s - d), min(goal, s)):
                total += prob(sp, k - 1) * one_d
            return total

    return [prob(s, goal) for s in range(goal, goal + d)]


@lru_cache(maxsize=10000)
def knight_survival(n, x, y, k):
    if x < 0 or x >= n or y < 0 or y >= n:
        return __zero
    elif k == 0:
        return __one
    return sum(knight_survival(n, x + dx, y + dy, k - 1) for (dx, dy) in __knight_moves) * __one_eighth


def bowling_score(frames):
    trans = {str(p): p for p in range(1, 10)}
    trans.update({'-': 0, 'X': 10})

    pins, prev = [], 0
    for curr in "".join(frames):
        pins.append(prev := trans.get(curr, 10 - prev))

    score, pos = 0, 0
    for _ in range(10):
        if pins[pos] == 10:
            score += 10 + pins[pos + 1] + pins[pos + 2]
            pos += 1
        else:
            both = pins[pos] + pins[pos + 1]
            score += both + (0 if both < 10 else pins[pos + 2])
            pos += 2
    return score


def word_board(board, words):
    n, found, visited = len(board), set(), set()

    def search(x_, y_, word_sofar):
        visited.add((x_, y_))
        idx = bisect_left(words, word_sofar)
        if idx < len(words) and words[idx].startswith(word_sofar):
            if words[idx] == word_sofar:
                found.add(word_sofar)
            for (dx, dy) in [(0, 1), (1, 0), (0, -1), (-1, 0)]:
                nx, ny = x_ + dx, y_ + dy
                if 0 <= nx < n and 0 <= ny < n and (nx, ny) not in visited:
                    search(nx, ny, word_sofar + board[nx][ny])
        visited.remove((x_, y_))

    for (x, y) in product(range(n), repeat=2):
        search(x, y, board[x][y])
    return sorted(found)


def lindenmayer(rules, n, start='A'):
    @lru_cache(maxsize=10000)
    def size(symbol_, k):
        return 1 if k == 0 else sum(size(cc, k - 1) for cc in rules[symbol_])

    # How many steps are needed to make result long enough to contain position n?
    steps, symbol = 0, start
    while size(start, steps) <= n:
        steps += 1

    # Find the position n in the correct branch of the Lindenmayer subtree.
    for step in range(steps, 0, -1):
        for symbol in rules[symbol]:
            skip = size(symbol, step - 1)
            if skip <= n:
                n -= skip
            else:
                break
    return symbol


def mian_chowla(i):
    global __lowest_unseen
    while i >= len(__mian_chowla):
        n = __mian_chowla[-1] + 1 + __lowest_unseen
        while True:
            for e in __mian_chowla:
                if n - e in __diffs_taken:
                    break
            else:  # Executed if previous loop didn't break
                break
            n += 1
        for e in __mian_chowla:
            __diffs_taken.add(n - e)
            while __lowest_unseen in __diffs_taken:
                __diffs_taken.remove(__lowest_unseen)
                __lowest_unseen += 1
        __mian_chowla.append(n)
    return __mian_chowla[i]


def costas_array(rows):
    n, dvs, placed = len(rows), set(), dict()
    to_fill = [row for (row, col) in enumerate(rows) if col is None]
    still_free = [True for _ in range(n)]

    def place_rook(row, col, undo_stack=None):
        for prev_row in placed:
            prev_col = placed[prev_row]
            dx, dy = row - prev_row, col - prev_col
            if (dx, dy) in dvs or (-dx, -dy) in dvs:
                return False
            dvs.add((dx, dy))
            if undo_stack is not None:
                undo_stack.append((dx, dy))
        placed[row] = col
        still_free[col] = False
        return True

    for (row, col) in enumerate(rows):
        if col is not None:
            if not place_rook(row, col):
                return False

    def fill_remaining():
        if len(to_fill) == 0:
            return True
        row = to_fill.pop()
        undo_stack = []
        for col in range(n):
            if still_free[col]:
                if place_rook(row, col, undo_stack):
                    if fill_remaining():
                        return True
                    still_free[col] = True
                    del placed[row]
                while len(undo_stack) > 0:
                    dvs.remove(undo_stack.pop())
        to_fill.append(row)
        return False

    return fill_remaining()


def topswops(perm):
    count_ = 0
    while perm[0] != 1:
        n = perm[0]
        first = tuple(reversed(perm[:n]))
        second = perm[n:]
        perm = first + second
        count_ += 1
    return count_


def sum_of_consecutive_squares(n):
    hi = 0
    while hi * hi < n:
        hi += 1
    lo, sum_ = hi, hi * hi
    while sum_ != n:
        if sum_ > n:  # Sum is too big, make it smaller
            sum_ -= hi * hi
            hi -= 1
            if hi < lo:
                lo, sum_ = hi, hi * hi
            if hi * (1 + hi) * (1 + 2 * hi) // 6 < n:  # Give up, if all squares up to hi are not enough
                return False
        else:  # Sum is too small, make it bigger
            lo -= 1
            sum_ += lo * lo
    return True


def is_chess_960(row):
    return row.find('b') % 2 != row.rfind('b') % 2 and row.find('r') < row.find('K') < row.rfind('r')


def queen_captures_all(queen, pawns):
    # Check whether pawn1 is located between queen and pawn2 on the board.
    # Assumes that queen, pawn1 and pawn2 are collinear.
    def is_between(queen_, pawn1, pawn2):
        if pawn2 is None:
            return True
        qx, qy = queen_
        px1, py1 = pawn1
        px2, py2 = pawn2
        return abs(px1 - qx) <= abs(px2 - qx) and abs(py1 - qy) <= abs(py2 - qy)

    # Returns the list of pawns nearest to queen to each of the eight directions.
    def list_nearest(queen_, pawns_):
        qx, qy = queen_
        nearest = [None] * 8
        for pawn in pawns_:
            px, py = pawn
            dx, dy = px - qx, py - qy
            if dx == 0 and dy > 0 and is_between(queen_, pawn, nearest[0]):
                nearest[0] = pawn  # N
            elif dx == 0 and dy < 0 and is_between(queen_, pawn, nearest[4]):
                nearest[4] = pawn  # S
            elif dy == 0 and dx > 0 and is_between(queen_, pawn, nearest[2]):
                nearest[2] = pawn  # E
            elif dy == 0 and dx < 0 and is_between(queen_, pawn, nearest[6]):
                nearest[6] = pawn  # W
            elif dy == dx and dx > 0 and is_between(queen_, pawn, nearest[1]):
                nearest[1] = pawn  # NE
            elif dy == dx and dx < 0 and is_between(queen_, pawn, nearest[5]):
                nearest[5] = pawn  # SW
            elif dy == -dx and dx > 0 and is_between(queen_, pawn, nearest[3]):
                nearest[3] = pawn  # SE
            elif dy == -dx and dx < 0 and is_between(queen_, pawn, nearest[7]):
                nearest[7] = pawn  # NW
        return [pawn for pawn in nearest if pawn is not None]

    # Recursive algorithm to determine whether queen can capture all pawns.
    def can_capture_all(queen_, pawns_):
        if len(pawns_) == 0:
            return True
        for pawn in list_nearest(queen_, pawns_):
            pawns_.remove(pawn)
            if can_capture_all(pawn, pawns_):
                return True
            pawns_.add(pawn)
        return False

    return can_capture_all(queen, set(pawns))


__add_cache = dict()


def addition_chain(n, brauer=False):
    if n < 3:
        return 0 if n < 2 else 1
    if not brauer:
        if n % 2 == 0 and n // 2 in __add_cache:
            best = __add_cache[n // 2] + 1
        else:
            best = addition_chain(n, True) + 1
    else:
        best = n * n

    def recurse(chain_):
        nonlocal best
        need, curr = 0, chain_[-1]
        nn, prev = curr, None
        while nn < n:
            nn, need = 2 * nn, need + 1
        if len(chain_) + need >= best:
            return False
        if curr == n:
            best = len(chain_)
            for (i, e) in enumerate(reversed(chain_)):
                if i > 1 and e * 2 != prev:
                    return False
                prev = e
            return True
        if n - curr in chain_:
            chain_.append(n)
            recurse(chain_)
            chain_.pop()
        else:
            i, tried = len(chain_) - 1, set()
            while i >= 1 and chain_[i] + chain_[i - 1] > curr:
                j = i
                while j >= 0 and curr < chain_[i] + chain_[j]:
                    new = chain_[i] + chain_[j]
                    if new <= n and new not in tried:
                        tried.add(new)
                        chain_.append(new)
                        if recurse(chain_):
                            return True
                        chain_.pop()
                    j -= 1
                i = 0 if brauer else i - 1

    recurse([1, 2])
    __add_cache[n] = best
    return best - 1


def count_deadwood(hand):
    big_M = 666
    hand = sorted([(__gin_ranks[rank], suit) for (rank, suit) in hand])
    hand_set = set(hand)
    # Counter for how many times each rank appears in hand
    rank_counts = [sum(1 for (r, s) in hand if r == rank) for rank in range(14)]
    best_overall = big_M

    def backtrack(pos, runs, sets, deadwood_sofar):
        nonlocal best_overall
        if deadwood_sofar >= best_overall:
            return big_M
        if pos == -1:
            if all(len(r) > 2 for r in runs) and all(len(s) > 2 for s in sets):
                best_overall = min(deadwood_sofar, best_overall)
                return 0
            else:
                return big_M
        (rank, suit) = hand[pos]
        if len(sets) > 0 and len(sets[-1]) < 3 and sets[-1][0][0] != rank:
            return big_M
        if len(runs) > 0 and len(runs[-1]) < 3 and runs[-1][-1][0] > rank + 1:
            return big_M
        rank_counts[rank] -= 1
        best = big_M

        # Join an existing run?
        was_run = False
        for r in runs:
            (rank2, suit2) = r[-1]
            if suit == suit2 and rank2 == rank + 1:
                was_run = True
                r.append((rank, suit))
                best = min(best, backtrack(pos - 1, runs, sets, deadwood_sofar))
                r.pop()
        # Start a new run
        if not was_run and (rank - 1, suit) in hand_set and (rank - 2, suit) in hand_set:
            runs.append([(rank, suit)])
            best = min(best, backtrack(pos - 1, runs, sets, deadwood_sofar))
            runs.pop()
        # Join an existing set?
        was_set = False
        for s in sets:
            (rank2, suit2) = s[-1]
            if rank2 == rank:
                was_set = True
                s.append((rank, suit))
                best = min(best, backtrack(pos - 1, runs, sets, deadwood_sofar))
                s.pop()
        # Start a new set?
        if not was_set and rank_counts[rank] > 1:
            sets.append([(rank, suit)])
            best = min(best, backtrack(pos - 1, runs, sets, deadwood_sofar))
            sets.pop()
        # Leave as deadwood?
        value = rank if rank < 10 else 10
        best = min(best, value + backtrack(pos - 1, runs, sets, deadwood_sofar + value))

        rank_counts[rank] += 1
        return best

    return backtrack(len(hand) - 1, [], [], 0)


def count_sevens(n):
    if n < 10:
        return 0 if n < 7 else 1
    nn = str(n)
    head, k = int(nn[0]), len(nn) - 1
    total = head * 10 ** (k - 1) * k + (10 ** k if head > 7 else 0)
    tail = int(nn[1:])
    tail_count = count_sevens(tail)
    return total + tail_count + (tail + 1 if head == 7 else 0)


def count_morse(message, letters):
    @lru_cache(maxsize=100000)
    def recurse(i, letters_):
        if i == len(message):
            return 1
        total = 0
        for (j, c) in enumerate(letters_):
            code = __morse_r[c]
            if message[i:i + len(code)] == code:
                total += recurse(i + len(code), letters_[:j] + letters_[j + 1:])
        return total

    return recurse(0, letters)


def othello_moves(othello, desdemona):
    os, ds, n = set(othello), set(desdemona), 8
    moves, dirs = [], [(0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1)]
    for x in range(n):
        for y in range(n):
            if (x, y) not in os and (x, y) not in ds:
                flipped = 0
                for (dx, dy) in dirs:
                    nx, ny, capture = x + dx, y + dy, 0
                    while 0 <= nx < n and 0 <= ny < n and (nx, ny) in ds:
                        nx, ny, capture = nx + dx, ny + dy, capture + 1
                    if capture > 0 and 0 <= nx < n and 0 <= ny < n and (nx, ny) in os:
                        flipped += capture
                if flipped > 0:
                    moves.append((x, y, flipped))
    return sorted(moves, key=lambda m: (-m[2], m[0], m[1]))


__liang = dict()


def liang_hyphenation(word, patterns):
    letters = 'abcdefghijklmnopqrstuvwxyz.'
    word = '.' + word + '.'
    if len(__liang) == 0:
        # Initialize the global pattern dictionary first time this function is called.
        for p in patterns:
            __liang["".join(c for c in p if c in letters)] = p
    n = len(word)
    counts = [0 for _ in range(n)]
    for i in range(n):
        for j in range(1, min(9, n - i + 1)):
            sub = word[i:i + j]
            if sub in __liang:
                pat, pos = __liang[sub], i
                for c in pat:
                    if c in letters:
                        pos += 1
                    else:
                        counts[pos] = max(counts[pos], int(c))
    result, word = "", word[1:-1]
    for (i, c) in enumerate(word):
        if 0 < i < len(word) - 1 and counts[i + 1] % 2 == 1:
            result += "-"
        result += c
    return result


def ordinal_transform(seed, i):
    first, seen, ordinal = True, dict(), []
    while i >= len(seed) + len(ordinal):
        start = 0 if first else len(seed) // 2
        end = min(len(seed), i - len(seed) + 1)
        for j in range(start, end):
            c = seed[j]
            seen[c] = seen.get(c, 0) + 1
            ordinal.append(seen[c])
        seed += ordinal
        first = False
    seed += ordinal
    return seed[i]


def staircase(digits):
    n = len(digits)

    @lru_cache(maxsize=n * n * n)
    def rec(prev, curr, i):
        if i == n:
            return 0
        dig = digits[i]
        curr2 = 10 * curr + int(dig)
        take = 1 + rec(curr2, 0, i + 1) if curr2 > prev else rec(prev, curr2, i + 1)
        while i < n and digits[i] == dig:
            i += 1
        leave = rec(prev, curr, i)
        return max(take, leave)

    return rec(-1, 0, 0)


def both_ways(text):
    pos = dict()
    for (i, e) in enumerate(text):
        if e in pos:
            pos[e].append(i)
        else:
            pos[e] = [i]
    m = 0
    for c in pos:
        pos_list = pos[c]
        nc = len(pos_list)
        if nc > 1:
            for ii in range(nc - 1):
                if pos_list[-1] - pos_list[ii] <= 2 * m:
                    break
                for jj in range(nc - 1, ii, -1):
                    i = pos_list[ii]
                    j = pos_list[jj]
                    if j - i > 2 * m:
                        k = 0
                        while i < j and text[i] == text[j]:
                            k, i, j = k + 1, i + 1, j - 1
                        m = max(m, k)
                    else:
                        break
    return m


def __gcd(a, b):
    while b > 0:
        a, b = b, a % b
    return a


def __strokes_needed(hole, c1, c2, best):
    # If we can use just the higher club, that is the optimal solution.
    if hole % c1 == 0:
        return hole // c1
    # If we can use just the lower club, improve the solution for now.
    if hole % c2 == 0:
        best = min(best, hole // c2)
    # Positive c1, positive c2.
    use1 = hole // c1
    while use1 > 0:
        remain = hole - c1 * use1
        if remain % c2 == 0:
            use2 = remain // c2
            best = min(best, use1 + use2)
            break
        use1 -= 1
    # Positive c1, negative c2.
    use1 = hole // c1 + 1
    while use1 < best:
        back = use1 * c1 - hole
        if back % c2 == 0:
            use2 = back // c2
            best = min(best, use1 + use2)
            break
        use1 += 1
    # Non-positive c1, positive c2.
    use2 = hole // c2 + 1
    while use2 < best:
        back = use2 * c2 - hole
        if back % c1 == 0:
            use1 = back // c1
            best = min(best, use1 + use2)
            break
        use2 += 1
    return best


def best_clubs(holes):
    best, c1_max, c1, c2 = sum(holes), max(holes), 2, 1
    while c1 <= c1_max:
        g = __gcd(c1, c2)
        if all(h % g == 0 for h in holes):
            score, remain = 0, len(holes) - 1
            for hole in holes:
                score += __strokes_needed(hole, c1, c2, best - score - remain)
                if score >= best:
                    break
                remain -= 1
            else:
                best = score
        c1, c2 = ((c1, c2+1) if c1 > c2 + 1 else (c1+1, 1))
    return best


def illuminate_all(lights):
    big = len(lights)

    @lru_cache(maxsize=10000)
    def illu(idx, owe, limit):
        if limit < 1:
            return big + 1
        if idx == -1:
            return 0 if owe < 1 else big + 1
        take = big
        if not (lights[idx] < owe or lights[idx] < -owe):
            take = 1 + illu(idx - 1, -lights[idx], limit - 1)
        leave = illu(idx - 1, owe + 1, take)
        return min(take, leave)

    return illu(big - 1, 0, big)


def verify_betweenness(perm, constraints):
    n = len(perm)
    inv = [0 for _ in range(n)]
    for (i, e) in enumerate(perm):
        inv[e] = i
    for (a, b, c) in constraints:
        ai, bi, ci = inv[a], inv[b], inv[c]
        if not (ai < bi < ci or ci < bi < ai):
            return False
    return True


def stepping_stones(n, ones):
    dirs = [(0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1)]
    filled = [[(x, y) in ones for y in range(n)] for x in range(n)]
    values = [[0 for _ in range(n)] for _ in range(n)]
    frontier = [set() for _ in range(n * n)]
    frontier[0] = set((x, y) for x in range(n) for y in range(n))

    def place(x, y, v):
        assert (x, y) in ones or (not filled[x][y] and values[x][y] == v)
        filled[x][y] = True
        modified = []
        for (dx, dy) in dirs:
            nx, ny = x + dx, y + dy
            if 0 <= nx < n and 0 <= ny < n and not filled[nx][ny]:
                ov = values[nx][ny]
                if ov + v < n * n:
                    values[nx][ny] += v
                    frontier[ov].remove((nx, ny))
                    frontier[ov + v].add((nx, ny))
                    modified.append((nx, ny, ov, True))
                else:
                    # Treat a cell with an impossibly large value as having already been filled.
                    filled[nx][ny] = True
                    modified.append((nx, ny, ov, False))
        return modified

    best_overall, best_list = 0, []

    def rec(v, so_far):
        nonlocal best_overall, best_list
        best = v - 1
        for (x, y) in list(frontier[v]):
            if not filled[x][y]:
                modified = place(x, y, v)
                so_far.append((x, y))
                best = max(best, rec(v + 1, so_far))
                if best > best_overall:
                    best_overall, best_list = best, so_far[:]
                filled[x][y] = False
                for (nx, ny, ov, moved) in modified:
                    if moved:
                        frontier[ov + v].remove((nx, ny))
                    else:
                        filled[nx][ny] = False
                    frontier[ov].add((nx, ny))
                    values[nx][ny] = ov
                so_far.pop()
        return best

    for (x, y) in ones:
        place(x, y, 1)
    return rec(2, [])


def laser_aliens(n, aliens):
    # Precompute sets of aliens in each row and column.
    row_aliens = [set() for _ in range(n)]
    col_aliens = [set() for _ in range(n)]
    for (row, col) in aliens:
        row_aliens[row].add(col)
        col_aliens[col].add(row)
    # Sort the rows based on how many aliens are on that row.
    rows = sorted(set(r for (r, c) in aliens), key=lambda r: -len(row_aliens[r]))

    best_solution = n

    # Recursive backtracking search to find the solution within given limit.
    def solve(row_idx, so_far):
        nonlocal best_solution
        # Negative and positive base cases of the recursion.
        if so_far >= best_solution:
            return
        if row_idx == len(rows):
            best_solution = min(best_solution, so_far)
            return
        curr_row = rows[row_idx]
        # Have all the aliens that were on this row been eliminated already?
        if len(row_aliens[curr_row]) == 0:
            return solve(row_idx + 1, so_far)
        # Try shooting one laser through this row, if there are at least two aliens.
        if len(row_aliens[curr_row]) > 1:
            solve(row_idx + 1, so_far + 1)
        # Try shooting laser through every column that has an alien on this row.
        if len(row_aliens[curr_row]) + so_far <= best_solution:
            undo_stack = []
            for c in row_aliens[curr_row]:
                for r in col_aliens[c]:
                    if r != curr_row:
                        undo_stack.append((r, c))
                        row_aliens[r].remove(c)
            solve(row_idx + 1, so_far + len(row_aliens[curr_row]))
            for (r, c_) in undo_stack:
                row_aliens[r].add(c_)
        # Didn't work either way.
        return False

    solve(0, 0)
    return best_solution


def domino_tile(rows):
    if sum(rows) % 2 == 1:
        return 0
    cached, sigs = [dict() for _ in rows], [0 for _ in rows]

    def count_fillings(row_idx, col_idx):
        w = rows[row_idx]
        # Find the first uncovered square starting from (row_idx, col_idx).
        while True:
            if col_idx >= w:
                # Current row has been fully filled, start filling above row.
                if row_idx > 0:
                    if sigs[row_idx - 1] in cached[row_idx - 1]:
                        return cached[row_idx - 1][sigs[row_idx - 1]]
                    else:
                        result = count_fillings(row_idx - 1, 0)
                        cached[row_idx - 1][sigs[row_idx - 1]] = result
                        return result
                else:
                    # The entire room has been filled.
                    return 1
            elif sigs[row_idx] & (2 ** col_idx) > 0:
                col_idx += 1
            else:
                break
        result = 0
        # Count the ways to complete filling with domino placed horizontally here.
        if col_idx < w - 1 and sigs[row_idx] & (2 ** (col_idx + 1)) == 0:
            result += count_fillings(row_idx, col_idx + 2)
        # Count the ways to complete filling with domino placed vertically here.
        if row_idx > 0 and col_idx < rows[row_idx - 1]:
            cc = 2 ** col_idx
            sigs[row_idx] += cc
            sigs[row_idx - 1] += cc
            result += count_fillings(row_idx, col_idx + 1)
            sigs[row_idx - 1] -= cc
            sigs[row_idx] -= cc
        # The total number of ways to complete the filling from this position.
        return result

    return count_fillings(len(rows) - 1, 0) if len(rows) > 1 else (1 if rows[0] % 2 == 0 else 0)


def cut_into_squares(a, b):
    if a == b:
        return 0
    a, b = max(a, b), min(a, b)
    return a - 1 if b == 1 else __cut(a, b)


@lru_cache(maxsize=10 ** 5)
def __cut(a, b):
    best = a * b
    for k in range(1, a // 2 + 1):
        best = min(best, 1 + cut_into_squares(k, b) + cut_into_squares(a - k, b))
    for k in range(1, b // 2 + 1):
        best = min(best, 1 + cut_into_squares(a, k) + cut_into_squares(a, b - k))
    return best


def collect_numbers(perm):
    rounds, prev_pos = 1, -1
    pos = [0 for _ in perm]
    for (i, e) in enumerate(perm):
        pos[e] = i
    for e in range(len(perm)):
        if pos[e] < prev_pos:
            rounds += 1
        prev_pos = pos[e]
    return rounds


def cut_corners(points):
    n, total, point_set = len(points), 0, set(points)
    pos = {p: i for (i, p) in enumerate(points)}
    corners, occurs, best_sol = [], {}, points
    for (i, (x, y)) in enumerate(points):
        j = i + 1
        while j < n and points[j][0] == x:
            h = points[j][1] - y
            if (x + h, y) in point_set:
                k = pos[(x + h, y)]
                corners.append((i, j, k))
                occurs[i] = occurs.get(i, 0) + 1
                occurs[j] = occurs.get(j, 0) + 1
                occurs[k] = occurs.get(k, 0) + 1
            j += 1

    corners.sort(key=lambda c: (occurs[c[0]] + occurs[c[1]] + occurs[c[2]], c))

    def recursive_cut(ci, removed, best_found):
        nonlocal best_sol
        if ci == -1:
            if len(removed) < len(best_sol):
                best_sol = sorted(removed)
            return len(removed)
        if len(removed) >= best_found:
            return len(removed)
        has_shared = False
        for i in corners[ci]:
            if i in removed:
                return recursive_cut(ci - 1, removed, best_found)
            if occurs[i] > 1:
                has_shared = True
        for (j_, i) in enumerate(corners[ci]):
            if occurs[i] > 1 or (not has_shared and j_ == 1):
                removed.add(i)
                curr = recursive_cut(ci - 1, removed, best_found)
                removed.remove(i)
                best_found = min(best_found, curr)
        return best_found

    return recursive_cut(len(corners) - 1, set(), len(points))


def count_corners(points):
    n, total, point_set = len(points), 0, set(points)
    for (i, (x, y)) in enumerate(points):
        j = i + 1
        while j < n and points[j][0] == x:
            h = points[j][1] - y
            if (x + h, y) in point_set:
                total += 1
            j += 1
    return total


def count_troikas(items):
    n, pos = len(items), dict()
    for (i, e) in enumerate(items):
        if e in pos:
            pos[e].append(i)
        else:
            pos[e] = [i]
    total = 0
    for e in pos:
        for (i, j) in combinations(pos[e], 2):
            k = i + 2 * (j - i)
            if k < n and items[k] == e:
                total += 1
    return total


def seven_zero(n):
    twos, fives = 0, 0
    # Divide away the factors of 2 and 5
    while n % 2 == 0:
        twos, n = twos + 1, n // 2
    while n % 5 == 0:
        fives, n = fives + 1, n // 5
    # Go through the numbers with consecutive sevens
    s = 7
    while s % n != 0:
        s = 10 * s + 7
    return s * (10 ** max(twos, fives))


def count_carries(a, b):
    carry_count, carry = 0, 0
    while a > 0 or b > 0:
        aa = a % 10
        bb = b % 10
        a = a // 10
        b = b // 10
        carry = (aa + bb + carry) > 9
        carry_count += carry
    return carry_count


def first_preceded_by_smaller(items, k=1):
    for i in range(k, len(items)):
        smaller_count = 0
        for j in range(i):
            if items[j] < items[i]:
                smaller_count += 1
                if smaller_count >= k:
                    return items[i]
    return None


def sort_by_digit_count(items):
    return list(sorted(items, key=lambda n: ([str(n).count(d) for d in "9876543210"], n)))


def leibniz(heads, pos):
    curr = []
    for h in heads:
        next_ = [h]
        for e in curr:
            next_.append(e - next_[-1])
        curr = next_
    result = []
    for i in pos:
        result.append(curr[i])
    return result


def candy_share(candies):
    rounds, n = 0, len(candies)
    while any(c > 1 for c in candies):
        from_left = [1 if candies[(i - 1) % n] > 1 else 0 for i in range(n)]
        from_right = [1 if candies[(i + 1) % n] > 1 else 0 for i in range(n)]
        from_ = [a + b for (a, b) in zip(from_left, from_right)]
        candies = [c - 2 if c > 1 else c for c in candies]
        candies = [a + b for (a, b) in zip(candies, from_)]
        rounds += 1
    return rounds


def __110(a, b, c):  # Rule 110 hardcoded
    return int((a, b, c) in ((1, 1, 0), (1, 0, 1), (0, 1, 1), (0, 1, 0), (0, 0, 1)))


def __110_forward(prev):  # For verification purposes of solutions for reverse_110
    n = len(prev)
    curr = [0 for _ in range(n)]
    for i in range(n):
        curr[i] = __110(prev[(i - 1) % n], prev[i], prev[(i + 1) % n])
    return curr


def __rec110(prev, curr):
    i = len(prev)
    if i > 2:
        if curr[i - 2] != __110(prev[-3], prev[-2], prev[-1]):
            return None
    if i == len(curr):
        if curr[i - 1] != __110(prev[-2], prev[-1], prev[0]):
            return None
        elif curr[0] != __110(prev[-1], prev[0], prev[1]):
            return None
        else:
            return prev
    for d in range(2):
        prev.append(d)
        result = __rec110(prev, curr)
        if result is not None:
            return result
        prev.pop()
    return None


def reverse_110(curr):
    result = __rec110([], curr)
    if result is not None:
        assert curr == __110_forward(result)
    return result


def hourglass_flips(glasses, tt):
    big_m = (tt * len(glasses)) ** 2  # Big M value to represent "no solution"

    def hourglass(ggs, t, limit, d=0):
        if limit < 0:
            return big_m, []
        ups = [u for (u, _) in ggs if u > 0]
        if t in ups:  # Can measure t from one hourglass.
            return 0, ["wait"]
        # Past the previous hurdle, we know that at least one flip will be needed.
        m = min(ups, default=0)  # Time before first glass runs out.
        if m == 0 or m > t:  # Impossible with the current hourglasses
            return big_m, None
        # New hourglasses after s minutes have elapsed.
        gs = [(u - min(u, m), d + min(u, m)) for (u, d) in ggs]
        # Which of these hourglasses are currently u/l symmetric?
        syms = [u == d for (u, d) in gs]
        # Best solution known for the current subproblem.
        best_, best_sol = big_m, None
        # Try out all subsets of hourglasses to flip.
        for flips in product([1, 0], repeat=len(ggs)):
            # Do not branch on flipping a currently u/l symmetric hourglass.
            if not any(ff and mm for (ff, mm) in zip(flips, syms)):
                fl = sum(flips)  # How many hourglasses are flipped this time.
                # Find the optimal way to measure the remaining time.
                (score, sol_) = hourglass([((d, u) if f else (u, d)) for ((u, d), f) in zip(gs, flips)],
                                          t - m,
                                          min(best_ - fl - 1, limit - fl),
                                          d + 1)
                if fl + score < best_:
                    best_, best_sol = fl + score, [flips] + sol_
        return best_, best_sol

    (best, sol) = hourglass(glasses, tt, limit=big_m)
    return best if best < big_m else None


def conjugate_regular(infinitive, subject, tense):
    replace = {
        'usted': 'él', 'ella': 'él', 'ello': 'él',
        'nosotras': 'nosotros', 'vosotras': 'vosotros',
        'ellas': 'ellos', 'ustedes': 'ellos'
    }

    subject = replace.get(subject, subject)

    presente_ar = {'yo': 'o', 'tú': 'as', 'él': 'a', 'nosotros': 'amos', 'vosotros': 'áis', 'ellos': 'an'}
    presente_er = {'yo': 'o', 'tú': 'es', 'él': 'e', 'nosotros': 'emos', 'vosotros': 'éis', 'ellos': 'en'}
    presente_ir = {'yo': 'o', 'tú': 'es', 'él': 'e', 'nosotros': 'imos', 'vosotros': 'ís', 'ellos': 'en'}

    preterito_ar = {'yo': 'é', 'tú': 'aste', 'él': 'ó', 'nosotros': 'amos', 'vosotros': 'asteis', 'ellos': 'aron'}
    preterito_er = {'yo': 'í', 'tú': 'iste', 'él': 'ió', 'nosotros': 'imos', 'vosotros': 'isteis', 'ellos': 'ieron'}

    imperfecto_ar = {'yo': 'aba', 'tú': 'abas', 'él': 'aba', 'nosotros': 'ábamos', 'vosotros': 'abais', 'ellos': 'aban'}
    imperfecto_er = {'yo': 'ía', 'tú': 'ías', 'él': 'ía', 'nosotros': 'íamos', 'vosotros': 'íais', 'ellos': 'ían'}

    futuro_all = {'yo': 'é', 'tú': 'ás', 'él': 'á', 'nosotros': 'emos', 'vosotros': 'éis', 'ellos': 'án'}

    to_use = {
        ('ar', 'presente'): presente_ar,
        ('er', 'presente'): presente_er,
        ('ir', 'presente'): presente_ir,
        ('ar', 'pretérito'): preterito_ar,
        ('er', 'pretérito'): preterito_er,
        ('ir', 'pretérito'): preterito_er,
        ('ar', 'imperfecto'): imperfecto_ar,
        ('er', 'imperfecto'): imperfecto_er,
        ('ir', 'imperfecto'): imperfecto_er,
    }

    # Future tense is formed by modifying the infinitive.
    if tense == 'futuro':
        result = infinitive + futuro_all[subject]
    # Present, past and imperfect past tenses are modified from stem.
    else:
        stem = infinitive[:-2]
        ending = infinitive[-2:]
        result = stem + to_use[(ending, tense)][subject]
    return result


def frequency_sort(items):
    counts = dict()
    for e in items:
        counts[e] = counts.get(e, 0) + 1
    return sorted(items, key=lambda x: (-counts.get(x), x))


def extract_increasing(digits):
    current, previous, result = 0, -1, []
    for d in digits:
        current = 10 * current + int(d)
        if current > previous:
            result.append(current)
            previous, current = current, 0
    return result


def josephus(n, k):
    soldiers, result = list(range(1, n + 1)), []
    while n > 0:
        pos = (k - 1) % n
        result.append(soldiers[pos])
        if pos == n - 1:
            soldiers.pop()
        else:
            soldiers = soldiers[pos + 1:] + soldiers[:pos]
        n -= 1
    return result


def brussels_choice_step(n, mink, maxk):
    result, nn = [], str(n)
    for i in range(0, len(nn) - mink + 1):
        for j in range(mink, maxk + 1):
            if i + j > len(nn):
                break
            left, m, right = nn[:i], nn[i:i + j], nn[i + j:]
            mm = int(m)
            result.append(int(f"{left}{2 * mm}{right}"))
            if mm % 2 == 0:
                result.append(int(f"{left}{mm // 2}{right}"))
    return sorted(result)


def fibonacci_sum(n):
    # Expand __fibs if necessary.
    while n > __fibs[-1]:
        __fibs.append(__fibs[-1] + __fibs[-2])

    # Use binary search to find the largest Fibonacci number <= n.
    i, result = bisect_left(__fibs, n), []

    # Extract Fibonacci numbers in descending order as they fit.
    while n > 0:
        if n >= __fibs[i]:
            result.append(__fibs[i])
            n -= __fibs[i]
            i -= 2
        else:
            i -= 1
    return result


def bridge_hand_shape(hand):
    counts = [0, 0, 0, 0]
    for (_, suit) in hand:
        counts[["spades", "hearts", "diamonds", "clubs"].index(suit)] += 1
    return counts


def hand_shape_distribution(hands):
    result = {}
    for hand in hands:
        hand_shape = tuple(reversed(sorted(bridge_hand_shape(hand))))
        result[hand_shape] = result.get(hand_shape, 0) + 1
    return result


def reverse_ascending_sublists(items):
    result, curr = [], []
    for x in chain(items, [None]):
        if x is not None and (curr == [] or curr[-1] < x):
            curr.append(x)
        else:
            curr.reverse()
            result.extend(curr)
            curr = [x]
    return result


def fractran(n, prog, giveup=1000):
    prog = [Fraction(a, b) for (a, b) in prog]
    result, step_count = [n], 0
    while step_count < giveup:
        for f in prog:
            v = n * f
            if v.denominator == 1:
                n = v.numerator
                step_count += 1
                result.append(n)
                break
        else:  # Executed if the previous loop didn't break
            break
    return result


def collapse_intervals(items):
    if not items:
        return ''
    result, consec, first = '', [], True
    for item in items:
        if consec == [] or item == consec[-1] + 1:
            consec.append(item)
        else:
            result += __encode_interval(consec, first)
            first = False
            consec = [item]
    result += __encode_interval(consec, first)
    return result


def __encode_interval(curr, first):
    result = '' if first else ','
    if len(curr) > 1:
        result += f"{curr[0]}-{curr[-1]}"
    else:
        result += str(curr[0])
    return result


def riffle(items, out=True):
    n, result = len(items) // 2, []
    for i in range(n):
        if out:
            result.append(items[i])
            result.append(items[n + i])
        else:
            result.append(items[n + i])
            result.append(items[i])
    return result


def expand_intervals(intervals):
    result = []
    if 0 < len(intervals):
        for item in intervals.split(","):
            items = item.split("-")
            result.extend(range(int(items[0]), int(items[-1]) + 1))
    return result


def nearest_smaller(items):
    n, res = len(items), []
    for (i, e) in enumerate(items):
        j = 1
        while i + j < n or i >= j:
            left = items[i - j] if i >= j else e
            right = items[i + j] if i + j < n else e
            ee = min(left, right)
            if ee < e:
                res.append(ee)
                break
            j += 1
        else:
            res.append(e)
    return res


def __word_match(word, letters):
    pos = 0
    for c in word:
        if c == letters[pos]:
            pos += 1
            if pos == len(letters):
                return True
    return False


def words_with_letters(words, letters):
    return [word for word in words if __word_match(word, letters)]


def possible_words(words, pattern):
    result = []
    for word in words:
        if len(word) == len(pattern):
            for (chw, chp) in zip(word, pattern):
                if chp == '*' and chw in pattern or chp != '*' and chp != chw:
                    break
            else:  # Executed if the previous loop didn't break
                result.append(word)
    return result


def reverse_vowels(text):
    vowels, result = [c for c in text if c in 'aeiouAEIOU'], ''
    for c in text:
        if c in 'aeiouAEIOU':
            ch = vowels.pop()
            result += ch.upper() if c in 'AEIOU' else ch.lower()
        else:
            result += c
    return result


def colour_trio(items):
    conv = {'rr': 'r', 'by': 'r', 'yb': 'r',
            'yy': 'y', 'rb': 'y', 'br': 'y',
            'bb': 'b', 'ry': 'b', 'yr': 'b'}
    goal = 1
    while goal * 3 < len(items):
        goal = goal * 3
    goal += 1
    items = [c for c in items]
    while len(items) > goal:
        items = [conv[items[i] + items[i+1]] for i in range(len(items)-1)]
    return conv.get(items[0] + items[-1])


def prominences(height):
    spots, m = [], -1
    for (i, e) in enumerate(height):
        left = height[i - 1] if i > 0 else 0
        right = height[i + 1] if i < len(height) - 1 else 0
        if left > e < right or left < e > right:
            spots.append(i)
        m = max(m, e)
    result = []
    for (j, i) in enumerate(spots):
        if height[i] == m:
            result.append((i, m, m))
        else:
            curr = height[i]
            k, left_low, right_low = j - 1, curr, curr
            while k >= -1:
                e = height[spots[k]] if k >= 0 else 0
                if e > curr:
                    break
                left_low = min(left_low, e)
                k -= 1
            k = j + 1
            while k <= len(spots):
                e = height[spots[k]] if k < len(spots) else 0
                if e > curr:
                    break
                right_low = min(right_low, e)
                k += 1
            prom = curr - max(left_low, right_low)
            if prom > 0:
                result.append((i, curr, prom))
    return result


def reach_corner(x, y, n, m, aliens):
    dirs = ((-1, 1), (1, 1), (1, -1), (-1, -1))
    aliens = set([(xx, yy) for (xx, yy) in aliens if (xx + yy) % 2 == (x + y) % 2])
    for (dx, dy) in dirs:
        moves, seen = 0, set()
        (bx, by) = (x, y)
        while True:
            if (bx, by) in aliens or (bx, by, dx, dy) in seen:
                break
            if (bx == 0 or bx == n - 1) and (by == 0 or by == m - 1):
                return True
            if bx == 0:
                dx = 1
            elif bx == n - 1:
                dx = -1
            if by == 0:
                dy = 1
            elif by == m - 1:
                dy = -1
            seen.add((bx, by, dx, dy))
            moves += 1
            bx, by = bx + dx, by + dy
    return False


def eliminate_neighbours(items):
    n = len(items)
    left = [0] * (n + 1)
    right = [0] * (n + 1)
    for (i, e) in enumerate(items):
        left[e] = items[i - 1] if i > 0 else 0
        right[e] = items[i + 1] if i < n - 1 else 0
    right[0], left[0] = items[0], items[-1]

    def eliminate(ee):
        if ee != 0:
            right[left[ee]] = right[ee]
            left[right[ee]] = left[ee]
            left[ee] = ee

    nb_count = 0
    for e in range(1, n + 1):
        if left[e] != e:
            nb_count += 1
            eliminate(left[e] if left[e] > right[e] else right[e])
            eliminate(e)
            if left[n] == n:
                return nb_count


def permutation_cycles(perm):
    perm, perms = perm[:], []
    for i in range(len(perm)):
        p = perm[i]
        if p > -1:
            curr, j, big = [], p, i
            while j != i:
                big = max(big, j)
                curr.append(j)
                j = perm[j]
            curr.append(j)
            j = curr.index(big)
            perms.append(curr[j:] + curr[:j])
            for j in curr:
                perm[j] = -1
    return sum(sorted(perms), start=[])


def brangelina(first, second):
    groups, prev = [], "X"
    for (i, c) in enumerate(first):
        if c in 'aeiou' and prev not in 'aeiou':
            groups.append(i)
        prev = c
    for (i, c) in enumerate(second):
        if c in 'aeiou':
            return first[:groups[0 if len(groups) == 1 else -2]] + second[i:]


# Return the list of possible wordomino moves in the given state.
def __wordomino_moves(state, words):
    prefix, moves = state[-3:], []
    # Find the first word that starts with the given three-letter prefix.
    i = bisect_left(words, prefix)
    # Advance from there over all the words that start with that prefix.
    while i < len(words) and words[i].startswith(prefix):
        word = words[i]
        # If this word works, its last letter is a legal move from the state.
        if word[1:] not in state:
            moves.append(word[-1])
        i += 1
    return moves


def wordomino(state, words, really_need_lowest=True):
    moves = __wordomino_moves(state, words)
    # Check if this state is a single move insta-win into a dead end.
    if not really_need_lowest:
        for c in moves:
            # If list of moves from successor (state+c) is empty, move there to win.
            if not __wordomino_moves(state + c, words):
                return c
    # If not insta-win, or if we need the lowest winning move, find the lowest winner.
    for c in moves:
        if not wordomino(state + c, words, False):
            return c
    # No winning moves exist from this state; this state is a cold loser.
    return None


def squares_intersect(s1, s2):
    (x1, y1, d1) = s1
    (x2, y2, d2) = s2
    return not (x1 + d1 < x2 or x2 + d2 < x1 or y1 + d1 < y2 or y2 + d2 < y1)


def __bulgarian_step(piles):
    return sorted([p - 1 for p in piles if p > 1] + [len(piles)])


def bulgarian_solitaire(piles, k):
    goal, move_count = list(range(1, k + 1)), 0
    piles.sort()
    while piles != goal:
        move_count += 1
        piles = __bulgarian_step(piles)
    return move_count


def bulgarian_cycle(piles):
    tortoise = hare = piles
    while True:
        # Tortoise moves one step per round.
        tortoise = __bulgarian_step(tortoise)
        # The hare moves two steps per round.
        hare = __bulgarian_step(__bulgarian_step(hare))
        if len(tortoise) == len(hare) and tortoise == hare:
            break
    count_ = 0
    while True:
        # Tortoise will crawl the loop while hare marks the spot.
        tortoise = __bulgarian_step(tortoise)
        count_ += 1
        if len(tortoise) == len(hare) and tortoise == hare:
            return count_


def count_overlapping_disks(disks):
    # Enter events for the same x-coordinate must be handled before
    # exit events, therefore 0 means enter, 1 means exit
    events = [(x - r, 0, (x, y, r)) for (x, y, r) in disks]
    events += [(x + r, 1, (x, y, r)) for (x, y, r) in disks]
    events.sort()
    overlap_count, active = 0, set()
    for (_, mode, (x, y, r)) in events:
        if mode == 0:
            for (xx, yy, rr) in active:
                if (xx - x) ** 2 + (yy - y) ** 2 <= (rr + r) ** 2:
                    overlap_count += 1
            active.add((x, y, r))
        else:
            active.remove((x, y, r))
    return overlap_count


def spread_the_coins(coins, left, right):
    pd = {i: c for (i, c) in enumerate(coins)}
    unstable = [i for (i, c) in enumerate(coins) if c >= left + right]

    def add_to(idx_, c):
        before = pd.get(idx_, 0)
        after = before + c
        pd[idx_] = after
        if before < left + right <= after:
            unstable.append(idx_)

    while len(unstable) > 0:
        idx = unstable.pop()
        c = pd.get(idx)
        k = c // (left + right)
        assert k > 0
        pd[idx] = c - k * (left + right)
        assert pd[idx] < left + right
        add_to(idx - 1, k * left)
        add_to(idx + 1, k * right)
    min_i = min((i for i in pd))
    max_i = max((i for i in pd))
    new_piles = [pd[i] for i in range(min_i, max_i + 1)]
    while new_piles[0] == 0:
        new_piles = new_piles[1:]
        min_i += 1
    return min_i, new_piles


def collatzy_distance(start, end):
    level = 0
    curr = [start]
    seen = set(curr)
    while end not in seen:
        level += 1
        succ = []
        for e in curr:
            for f in [lambda y: 3 * y + 1, lambda y: y // 2]:
                x = f(e)
                if x not in seen:
                    succ.append(x)
                    seen.add(x)
        curr = succ
    return level


def crag_score(dice):
    dice.sort()
    if sum(dice) == 13:
        return 50 if dice[0] == dice[1] or dice[1] == dice[2] else 26
    if dice[0] == dice[2]:
        return 25
    if dice in ([1, 2, 3], [4, 5, 6], [1, 3, 5], [2, 4, 6]):
        return 20
    return max(pip * dice.count(pip) for pip in dice)


def __crag_value(dice, category):
    s = sum(dice)
    if category == 0:  # Crag
        if s == 13 and (dice[0] == dice[1] or dice[1] == dice[2]):
            return 50
        else:
            return 0
    elif category == 1:  # Thirteen
        return 26 if s == 13 else 0
    elif category == 2:  # Three of a kind
        return 25 if dice[0] == dice[2] else 0
    elif category == 3:  # Low straight
        return 20 if dice == [1, 2, 3] else 0
    elif category == 4:  # High straight
        return 20 if dice == [4, 5, 6] else 0
    elif category == 5:  # Odd straight
        return 20 if dice == [1, 3, 5] else 0
    elif category == 6:  # Even straight
        return 20 if dice == [2, 4, 6] else 0
    else:  # Pip values
        pip = 13 - category  # pip value to add up
        return sum(x for x in dice if x == pip)


def __crag_score_rec(rolls, limit, cats, i, to_beat):
    if i == len(rolls) or to_beat >= limit[i]:
        return 0
    best, poss = 0, [(__crag_value(rolls[i], cat), cat) for cat in cats]
    poss.sort(reverse=True)
    for (curr, cat) in poss:
        cats.remove(cat)
        curr += __crag_score_rec(rolls, limit, cats, i + 1, best - curr)
        best = max(best, curr)
        cats.add(cat)
        if best == limit[i]:
            break
    return best


def optimal_crag_score(rolls):
    rolls = [sorted(dice) for dice in rolls]
    rolls.sort(key=lambda dice: crag_score(dice), reverse=True)
    limit = [crag_score(dice) for dice in rolls]
    for i in range(len(rolls) - 2, -1, -1):
        limit[i] += limit[i + 1]
    result = __crag_score_rec(rolls, limit, set(range(13)), 0, 0)
    return result


def substitution_words(pattern, words):
    n, result = len(pattern), []
    for word in words:
        if len(word) == n:
            subs, taken = dict(), set()
            for (c1, c2) in zip(word, pattern):
                if c1 in subs:
                    if subs[c1] != c2:
                        break
                else:
                    if c2 in taken:
                        break
                    else:
                        taken.add(c2)
                        subs[c1] = c2
            else:  # Executed if there was no break in previous loop
                result.append(word)
    return result


def __prime_code(word):
    m = 1
    for c in word:
        m *= __primes[ord(c) - ord('a')]
    return m


def unscramble(words, word):
    result, first, last, g = [], word[0], word[-1], __prime_code(word)
    start = bisect_left(words, first)
    end = bisect_left(words, chr(ord(first) + 1))
    for i in range(start, end):
        w = words[i]
        if len(w) == len(word) and w[-1] == last and __prime_code(w) == g:
            result.append(w)
    return result


def words_with_given_shape(words, shape):
    result = []
    for word in words:
        if len(word) == len(shape) + 1:
            for i in range(len(word) - 1):
                sign = ord(word[i+1]) - ord(word[i])
                if (sign < 0 and shape[i] != -1) or (sign == 0 and shape[i] != 0) or (sign > 0 and shape[i] != 1):
                    break
            else:
                result.append(word)
    return result


def autocorrect_word(word, words, df):
    best, bd = '', 10 ** 100
    for w in words:
        if len(w) == len(word):
            d = sum((df(c1, c2) for (c1, c2) in zip(w, word)))
            if d < bd:
                bd, best = d, w
    return best


def remove_after_kth(items, k=1):
    result, seen = [], dict()
    for e in items:
        s = seen.get(e, 0) + 1
        if s <= k:
            result.append(e)
        seen[e] = s
    return result


def ztalloc(pattern):
    curr = 1
    for c in reversed(pattern):
        if c == 'd':
            curr = 2 * curr
        else:
            if (curr - 1) % 3 != 0:
                return None
            else:
                curr = (curr - 1) // 3
                if curr % 2 == 0:
                    return None
    return curr


def duplicate_digit_bonus(n):
    total, prev, tally, first = 0, -1, 0, 2
    while n >= 0:
        d = n % 10 if n > 0 else -1
        n = n // 10 if n > 0 else -1
        if d == prev:
            tally += 1
        else:
            if tally > 0 and prev > -1:
                add = (10 ** (tally - 1)) * (2 if first > 0 else 1)
                total += add
            first -= 1
            prev, tally = d, 0
    return total


def ryerson_letter_grade(n):
    if n < 50:
        return 'F'
    elif n > 89:
        return 'A+'
    elif n > 84:
        return 'A'
    elif n > 79:
        return 'A-'
    tens = n // 10
    ones = n % 10
    if ones < 3:
        adjust = "-"
    elif ones > 6:
        adjust = "+"
    else:
        adjust = ""
    return "DCB"[tens - 5] + adjust


def manhattan_skyline(towers):
    # Collect events into a list; 0 means enter, 1 means exit. We need
    # to store the building number i to distinguish between overlapping
    # active buildings with the same height.
    events = [(s, 0, i, h) for (i, (s, e, h)) in enumerate(towers)]
    events += [(e, 1, i, h) for (i, (s, e, h)) in enumerate(towers)]
    events.sort()  # Sort the events in ascending x-order, entries first.
    total_area = 0  # Count of total area.
    prev_x = 0  # The x-coordinate of the previous event.
    active = set()  # The active buildings currently in the sweep view.
    tallest = 0  # The height of the tallest active building.
    for (x, mode, i, h) in events:
        # Add the area from the slab between these events. If either
        # slab width or the tallest building height is zero, this
        # product is also zero and the total area does not change.
        total_area += (x - prev_x) * tallest
        # Update the active set depending on what happens.
        if mode == 0:  # Building i enters the active view.
            active.add((i, h))
            tallest = max(tallest, h)  # May need to update tallest.
        else:  # Building i exits the active view.
            active.remove((i, h))
            if h == tallest:  # Compute new tallest from scratch.
                tallest = max((hh for (_, hh) in active)) if len(active) > 0 else 0
        prev_x = x
    return total_area


def is_ascending(items):
    prev = None
    for x in items:
        if prev is not None and prev >= x:
            return False
        prev = x
    return True


def count_dominators(items):
    dominators = []
    for e in items:
        # Pop out the previous dominators that don't dominate this one.
        while len(dominators) > 0 and dominators[-1] <= e:
            dominators.pop()
        dominators.append(e)
    return len(dominators)


def arithmetic_progression(elems):
    best, e_set, n, tabu = (elems[0], 0, 1), set(elems), len(elems), set()
    for i, e1 in enumerate(elems):
        if best is not None and best[2] > n - i:
            break
        for j in range(i + 1, n):
            e2 = elems[j]
            step = e2 - e1
            if (e1, step) not in tabu:
                k = 1
                while e2 in e_set:
                    tabu.add((e2, step))
                    k += 1
                    e2 += step
                if best is None or best[2] < k:
                    best = (e1, step, k)
    return best


def __is_word(words, word):
    idx = bisect_left(words, word)
    return 0 <= idx < len(words) and words[idx] == word


def word_height(words, word):
    if not __is_word(words, word):
        return 0
    best, n = 1, len(word)
    for i in range(1, n):
        left, right = word[:i], word[i:]
        left_height = word_height(words, left)
        if left_height > 0:
            right_height = word_height(words, right)
            if right_height > 0:
                best = max(best, 1 + max(left_height, right_height))
    return best


def max_checkers_capture(n, x, y, pieces):
    best = 0
    for (dx, dy) in [(-1, +1), (+1, +1), (+1, -1), (-1, -1)]:
        if 0 <= x + 2 * dx < n and 0 <= y + 2 * dy < n:
            if (x + 2 * dx, y + 2 * dy) not in pieces and (x + dx, y + dy) in pieces:
                pieces.remove((x + dx, y + dy))
                capture = max_checkers_capture(n, x + 2 * dx, y + 2 * dy, pieces)
                best = max(best, 1 + capture)
                pieces.add((x + dx, y + dy))
    return best


def count_growlers(animals):
    growl = 0
    for aa in [animals, [a[::-1] for a in reversed(animals)]]:
        balance = 0
        for pos, a in enumerate(aa):
            if balance > 0 and (a == 'cat' or a == 'dog'):
                growl += 1
            balance -= 1 if a == 'cat' or a == 'tac' else -1
    return growl


def count_maximal_layers(points):
    points.sort(key=lambda x: x[0] + x[1])
    layers = 0
    while len(points) > 0:
        layers += 1
        keep = []
        for i, p in enumerate(points):
            for j in range(i+1, len(points)):
                if __dominated(p, points[j]):
                    keep.append(p)
                    break
        points = keep
    return layers


def line_with_most_points(points):
    most, tabu = 0, set()
    for i, p1 in enumerate(points):
        for j in range(i + 1, len(points)):
            if (i, j) not in tabu:
                p2 = points[j]
                point_count = 2
                for k in range(j + 1, len(points)):
                    p3 = points[k]
                    if __collinear(*p1, *p2, *p3):
                        tabu.add((i, k))
                        tabu.add((j, k))
                        point_count += 1
                most = max(most, point_count)
    return most


def midnight(dice):
    best = 0

    def midnight_rec(dice_, remain, chosen_dice_blocks, tally_so_far):
        nonlocal best

        if best - tally_so_far >= sum([6, 5, 4, 3, 2, 1][:len(remain)]):
            return 0
        if len(remain) == 0:
            has_one, has_four, total = False, False, 0
            for level, s in enumerate(chosen_dice_blocks):
                for d in s:
                    pips = dice_[d][level]
                    if pips == 1:
                        has_one = True
                    if pips == 4:
                        has_four = True
                    total += pips
            best = max(best, total - 5 if has_one and has_four else 0)
        else:
            level = len(chosen_dice_blocks)
            remain.sort(key=lambda d_: -dice_[d_][level])
            for r in range(1, len(remain) + 1):
                for block in combinations(remain, r):
                    new_remain = [d for d in remain if d not in block]
                    new_tally = tally_so_far
                    for d in block:
                        new_tally += dice_[d][level]
                    chosen_dice_blocks.append(block)
                    midnight_rec(dice_, new_remain, chosen_dice_blocks, new_tally)
                    chosen_dice_blocks.pop()
            return best

    midnight_rec(dice, list(range(6)), [], 0)
    return best


def tukeys_ninthers(items):
    while len(items) > 2:
        items = [sorted(items[i-2:i+1])[1] for i in range(2, len(items), 3)]
    return items[0]


def is_perfect_power(n):
    p = 2
    while 2 ** p <= n:
        i, j = 2, n // p
        while i < j:
            m = (i + j) // 2
            if m ** p < n:
                i = m + 1
            else:
                j = m
        if i ** p == n:
            return True
        p += 1
    return False


def rooks_with_friends(n, friends, enemies):
    safe = [[1 for _ in range(n)] for _ in range(n)]
    dirs = [(0, 1), (1, 0), (0, -1), (-1, 0)]
    for (rx, ry) in enemies:
        for (dx, dy) in dirs:
            safe[rx][ry], nx, ny = 0, rx + dx, ry + dy
            while (0 <= nx < n and 0 <= ny < n and
                   (nx, ny) not in friends and (nx, ny) not in enemies):
                safe[nx][ny] = 0
                nx, ny = nx + dx, ny + dy
    return sum((sum(row) for row in safe)) - len(friends)


def safe_squares_rooks(n, rooks):
    saferow = [1 for _ in range(n)]
    safecol = [1 for _ in range(n)]
    for (row, col) in rooks:
        saferow[row] = safecol[col] = 0
    return sum(saferow) * sum(safecol)


def safe_squares_bishops(n, bishops):
    safe_count = 0
    for row in range(n):
        for col in range(n):
            if (row, col) not in bishops:
                for (br, bc) in bishops:
                    if abs(br - row) == abs(bc - col):
                        break
                else:
                    safe_count += 1
    return safe_count


def balanced_ternary(n, pp=None, sp=None):
    if abs(n) < 2:
        return [[-1], [], [1]][n + 1]
    if n < 0:
        return [-x for x in balanced_ternary(-n, pp, sp)]
    if not pp:
        pp, sp = 1, 0
        while 3 * pp <= n:
            sp += pp
            pp = 3 * pp
    else:
        while pp > n:
            pp = pp // 3
            sp = sp - pp
    if n <= pp + sp:
        return [pp] + balanced_ternary(n - pp, pp // 3, sp - pp // 3)
    else:
        return [3 * pp] + balanced_ternary(n - 3 * pp, pp, sp)


def __two_summers(items, goal, i=None, j=None):
    # Initialize the approaching indices, unless given.
    if i is None:
        i = 0
    if j is None:
        j = len(items) - 1
    # Each round, one index takes one step towards the other.
    while i < j:
        x = items[i] + items[j]
        if x == goal:
            return True
        elif x < goal:
            i += 1
        else:
            j -= 1
    return False


# With __two_summers, finding three summers is now just one loop.

def three_summers(items, goal):
    for i in range(len(items) - 2):
        if __two_summers(items, goal - items[i], i + 1):
            return True
    return False


def count_divisibles_in_range(start, end, n):
    if start < 0 and end <= 0:
        return count_divisibles_in_range(-end, -start, n)
    elif start < 0:
        return count_divisibles_in_range(0, -start, n) + count_divisibles_in_range(1, end, n)
    else:
        if start % n > 0:
            start += (n - start % n)
        end -= end % n
        return 0 if start > end else 1 + (end - start) // n


def lattice_paths(x, y, tabu):
    if (0, 0) in tabu:
        return 0
    path_count = [[0 for _ in range(y + 1)] for _ in range(x + 1)]
    path_count[0][0] = 1
    for xx in range(x + 1):
        for yy in range(y + 1):
            if (xx, yy) != (0, 0) and (xx, yy) not in tabu:
                down = 0 if yy == 0 else path_count[xx][yy - 1]
                left = 0 if xx == 0 else path_count[xx - 1][yy]
                path_count[xx][yy] = down + left
    return path_count[x][y]


def winning_card(cards, trump=None):
    winner = cards[0]
    for idx in range(1, 4):
        curr = cards[idx]
        if winner[1] != trump and curr[1] == trump:
            winner = curr
        elif winner[1] == curr[1] and __bridge_ranks[winner[0]] < __bridge_ranks[curr[0]]:
            winner = curr
    return winner


def oware_move(board, pos):
    n, captured, orig = len(board), 0, pos
    sow = board[pos]
    board[pos] = 0
    while sow > 0:
        pos = (pos + 1) % n
        if pos != orig:
            board[pos] += 1
            sow -= 1
    while pos >= n // 2 and 2 <= board[pos] <= 3:
        captured += board[pos]
        board[pos] = 0
        pos = (pos - 1) % n
    return board


def __lunar_add(a, b):
    if a == 0:
        return b
    elif b == 0:
        return a
    else:
        return 10 * __lunar_add(a // 10, b // 10) + max(a % 10, b % 10)


def __sd_mul(a, b):
    return 0 if b == 0 else 10 * __sd_mul(a, b // 10) + min(a, b % 10)


def lunar_multiply(a, b):
    return 0 if a == 0 else __lunar_add(__sd_mul(a % 10, b), 10 * lunar_multiply(b, a // 10))


def __cookie(piles, dl, bl):
    if dl < 1:
        return None
    n = len(piles)
    if n == 1:
        return [piles[0]]
    decor = [((i + 1) * e, e) for (i, e) in enumerate(reversed(piles))]
    for (drop, e) in islice(sorted(decor, reverse=True), bl):
        new_piles = [c - (e if e <= c else 0) for c in piles]
        new_piles = sorted(set([c for c in new_piles if c > 0]))
        rest = __cookie(new_piles, dl - 1, bl)
        if rest is not None:
            return [e] + rest
    return None


def cookie(piles):
    dl, bl, bestd, best, total = 1, 1, len(piles) + 1, None, 1
    while total <= len(piles) + bestd:
        total += 1
        for d in range(1, min(total, bestd)):
            dl, bl = d, total - d
            result = __cookie(piles, dl, bl)
            if result:
                bestd, best = dl, result
                break
    return len(best)


def scylla_or_charybdis(seq, n):
    k, best, best_k = 1, None, None
    while k <= len(seq) // n:
        pos, move_count = 0, 0
        for m in seq[k-1::k]:
            move_count += 1
            pos += 1 if m == '+' else -1
            if abs(pos) == n:
                if best is None or best > move_count:
                    best, best_k = move_count, k
                break
        k += 1
    return best_k


def counting_series(n):
    d, i, i_prev, b = 0, 0, 0, 9
    while i <= n:
        i_prev = i
        d += 1
        i += d * b
        b *= 10
    n -= i_prev
    return int(str(n // d + 10 ** (d-1))[n % d])


def taxi_zum_zum(moves):
    pos, heading, dv = (0, 0), 0, [(0, 1), (-1, 0), (0, -1), (1, 0)]
    for m in moves:
        if m == 'R':
            heading = (heading + 3) % 4
        elif m == 'L':
            heading = (heading + 1) % 4
        else:
            pos = (pos[0] + dv[heading][0], pos[1] + dv[heading][1])
    return pos


def is_left_handed(pips):
    # How many sides need to be mirrored to get to 123?
    flip = len([p for p in pips if p > 3]) % 2
    # Mirror the sides that are not 123.
    pips = [p if p < 4 else 7 - p for p in pips]
    # Is the resulting die clockwise?
    left = pips in ([1, 2, 3], [2, 3, 1], [3, 1, 2])
    # Flip the result if needed.
    return left if not flip else not left


def group_and_skip(n, a, b=1):
    result = []
    while n > 0:
        k = n // a
        result.append(n % a)
        n = b * k
    return result


def trips_fill(words, pat, tabu):
    if len(pat) < 3:
        return pat
    if pat[0] == '*':
        start, end = 0, len(words)
    elif pat[1] == '*':
        ch = pat[0]
        start, end = bisect_left(words, ch), bisect_left(words, chr(ord(ch) + 1))
    else:
        start = bisect_left(words, pat[:2])
        end = start + 1
        while end < len(words) and words[end].startswith(pat[:2]):
            end += 1
    if start < len(words):
        for i in range(start, end):
            w = words[i]
            if w not in tabu:
                m0 = pat[0] == '*' or w[0] == pat[0]
                m1 = pat[1] == '*' or w[1] == pat[1]
                m2 = pat[2] == '*' or w[2] == pat[2]
                if m0 and m1 and m2:
                    tabu.append(w)
                    tail = trips_fill(words, w[1:3] + pat[3:], tabu)
                    tabu.pop()
                    if tail:
                        return w[0] + tail


def mcculloch(digits):
    if len(digits) > 1:
        head, tail = digits[0], digits[1:]
        if head == '2':
            return tail
        if head in '345':
            value = mcculloch(tail)
            if value:
                if head == '3':
                    return f"{value}2{value}"
                elif head == '4':
                    return value[::-1]
                elif head == '5':
                    return f"{value}{value}"


def __canonize(ranks_):
    return '-' if not ranks_ else "".join([__faces.get(r, 'x') for r in ranks_])


def bridge_hand_shorthand(hand):
    sol = [[__bridge_ranks[r] for (r, s) in hand if s == suit] for suit in __suits]
    return " ".join([__canonize(sorted(suit, reverse=True)) for suit in sol])


def losing_trick_count(hand):
    short = bridge_hand_shorthand(hand).replace('J', 'x')
    return sum([__losers.get(s[:3], len(s[:3])) for s in short.split(" ")])


def knight_jump(steps, start, end):
    return steps == tuple(sorted((abs(x - y) for (x, y) in zip(start, end)), reverse=True))


def sum_of_distinct_cubes(n):
    def sdc_rec(n_, k_):
        if n_ == 0:
            return []
        if n_ < 0 or k_ < 1:
            return None
        while k_ > 0:
            ans = sdc_rec(n_ - k_ ** 3, k_ - 1)
            if ans is not None:
                ans.append(k_)
                return ans
            k_ -= 1
        return None

    result = sdc_rec(n, int(n ** (1/3)))
    return result[::-1] if result is not None else None


def wythoff_array(n):
    prev = None  # First two elements of the previous row.
    lowest_unseen = 1  # The smallest positive integer not yet seen.
    seen = set()  # Integers > lowest_unseen that we have already seen.
    for r in count(0):  # Row number that is being generated.
        if r == 0:  # First two elements of the first row.
            e2, e3 = 1, 2
        else:  # First two elements of the next row.
            e2 = lowest_unseen
            e3 = prev[1] + (3 if e2 - prev[0] == 2 else 5)
        # Initialize the state variables for the current row.
        prev, e1, c = (e2, e3), e3 - e2, 0
        # Generate elements in the current row up to n.
        while e2 <= n:
            if e2 == n:  # Found what we are looking for
                return r, c
            # Update the set of integers that we have seen.
            seen.add(e2)
            # Release the elements less than the smallest unseen.
            while lowest_unseen in seen:
                seen.remove(lowest_unseen)
                lowest_unseen += 1
            # Move one step to the right in the current row.
            e2, e1, c = e2 + e1, e2, c + 1


def pyramid_blocks(n, m, h):
    return h * (1 - 3 * h + 2 * h * h - 3 * m + 3 * h * m - 3 * n + 3 * h * n + 6 * m * n) // 6


def count_and_say(digits):
    result, prev, digit_count = '', '$', 0
    for d in chain(digits, ['$']):
        if d == prev:
            digit_count += 1
        else:
            if prev != '$':
                result += str(digit_count)
                result += prev
            prev = d
            digit_count = 1
    return result


def is_cyclops(n):
    n, h = str(n), len(str(n)) // 2
    return len(n) == 2 * h + 1 and n[h] == '0' and '0' not in n[:h] and '0' not in n[h + 1:]


def milton_work_point_count(hand, trump='notrump'):
    score, values = 0, {'ace': 4, 'king': 3, 'queen': 2, 'jack': 1}
    for (rank, suit) in hand:
        score += values.get(rank, 0)
    shape = bridge_hand_shape(hand)
    if list(sorted(shape)) == [3, 3, 3, 4]:
        score -= 1
    strains = ['spades', 'hearts', 'diamonds', 'clubs', 'notrump']
    if trump != 'notrump':
        for (strain, s) in zip(strains, shape):
            if strain != trump and s < 2:
                score += [5, 3][s]
    for s in shape:
        if s == 5:
            score += 1
        elif s == 6:
            score += 2
        elif s >= 7:
            score += 3
    return score


def __dominated(p1, p2):
    return p1[0] < p2[0] and p1[1] < p2[1]


def __cross(x1, y1, x2, y2, x3, y3):
    return (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1)


def __collinear(x1, y1, x2, y2, x3, y3):
    return __cross(x1, y1, x2, y2, x3, y3) == 0


def sum_of_two_squares(n):
    a, b = 1, 1
    while a * a < n:
        a += 1
    while a >= b:
        d = a * a + b * b
        if d == n:
            return a, b
        elif d < n:
            b += 1
        else:
            a -= 1
    return None


def count_squares(points):
    pts, squares = set(points), 0
    xmax = max(x for (x, y) in points)
    ymax = max(y for (x, y) in points)
    for (x, y) in points:
        for xd in range(0, xmax - x + 1):
            for yd in range(1, ymax - y + 1):
                c1 = (x + xd, y + yd) in pts
                c2 = (x + yd, y - xd) in pts
                c3 = (x + yd + xd, y - xd + yd) in pts
                if c1 and c2 and c3:
                    squares += 1
    return squares


def only_odd_digits(n):
    return all((c not in '02468') for c in str(n))


def __expand_primes(n):
    # Start looking for new primes after the largest prime we know.
    m = __primes[-1] + 2
    while n > __primes[-1]:
        if __is_prime(m):
            __primes.append(m)
        m += 2


def __is_prime(n):
    # To check whether n is prime, check its divisibility with
    # all known prime numbers up to the square root of n.
    # First ensure that we have enough primes to do the test.
    while __primes[-1] ** 2 < n:
        __expand_primes((__primes[-1] + 1) ** 2)

    for d in __primes:
        if n % d == 0:
            return False
        if d * d > n:
            return True
    return True


def __f_sum(n, i, factors):
    for f in factors:
        if n % f == 0:
            return True
    if i >= len(factors):
        return False
    p = factors[i]
    if n % p == 0:
        return True
    if n < p:
        return False
    else:
        return __f_sum(n - p, i, factors) or __f_sum(n, i + 1, factors)


def balanced_centrifuge(n, k):
    factors = []
    __expand_primes(n)
    for p in __primes:
        if n % p == 0:
            factors.append(p)
        if p > n:
            break
    return __f_sum(k, 0, factors) and __f_sum(n - k, 0, factors)


def fibonacci_word(k):
    while k > __fibs[-1]:
        __fibs.append(__fibs[-1] + __fibs[-2])
    i = len(__fibs) - 1
    while k > 1:
        if k >= __fibs[i - 1]:
            k = k - __fibs[i - 1]
        i = i - 1
    return str(k)


def can_balance(items):
    for i in range(1, len(items)-1):
        left_torque = sum([(i-j) * items[j] for j in range(0, i)])
        right_torque = sum([(j-i) * items[j] for j in range(i+1, len(items))])
        if left_torque == right_torque:
            return i
    return -1


def postfix_evaluate(items):
    stack = []
    for item in items:
        if type(item) == str:
            o2 = stack.pop()
            o1 = stack.pop()
            if item == '+':
                stack.append(o1 + o2)
            elif item == '-':
                stack.append(o1 - o2)
            elif item == '*':
                stack.append(o1 * o2)
            elif item == '/':
                stack.append(o1 // o2 if o2 != 0 else 0)
        else:
            stack.append(item)
    return stack[0]


def give_change(amount, coins):
    result = []
    for coin in coins:
        use, amount = amount // coin, amount % coin
        result.extend([coin] * use)
    return result


def nearest_polygonal_number(n, s):
    def pg(i, ss):
        return ((ss-2) * i * (i-1)) // 2 + i

    a, b = 1, 2
    while pg(b, s) < n:
        a, b = b, 10 * b
    while b - a > 1:
        m = (a+b) // 2
        v = pg(m, s)
        if v < n:
            a = m
        else:
            b = m
    va, vb = pg(a, s), pg(b, s)
    da, db = abs(n-va), abs(n-vb)
    return va if da <= db else vb


def hitting_integer_powers(a, b, t=100):
    pa, pb, aa, bb = 1, 1, a, b
    while t * abs(aa - bb) > min(aa, bb):
        if aa < bb:
            aa = aa * a
            pa += 1
        else:
            bb = bb * b
            pb += 1
    return pa, pb


def __frog1d(x1, d1, x2, d2):
    if x1 > x2:
        (x1, d1, x2, d2) = (x2, d2, x1, d1)
    d, dx = x2 - x1, d1 - d2
    if d > 0 >= dx:
        return None
    if d == 0:
        return 0 if dx == 0 else None
    return d // dx if (dx != 0 and d % dx == 0) else None


def frog_collision_time(frog1, frog2):
    (x1, y1, dx1, dy1) = frog1
    (x2, y2, dx2, dy2) = frog2
    tx = __frog1d(x1, dx1, x2, dx2)
    if tx is not None:
        ty = __frog1d(y1, dy1, y2, dy2)
        if ty is not None:
            if tx == 0 or ty == 0:
                result = max(tx, ty)
            else:
                result = tx if tx == ty else None
            return result if result and result > 0 else None


def subtract_square(queries):
    pos, heat, result = 0, [False, True], []
    if queries[pos] == 0:
        result = [False]
        pos += 1
    if queries[pos] == 1:
        result.append(True)
        pos += 1
    curr = 2
    while pos < len(queries):
        i = 1
        while i * i <= curr:
            if not heat[curr - i * i]:
                heat.append(True)
                break
            i += 1
        else:
            heat.append(False)
        if curr == queries[pos]:
            result.append(heat[-1])
            pos += 1
        curr += 1
    return result


def calkin_wilf(n):
    q, m = deque(), 1
    q.append(Fraction(1, 1))
    while m < n:
        f = q.popleft()
        num, den = f.numerator, f.denominator
        q.append(Fraction(num, num + den))
        q.append(Fraction(num + den, den))
        m += 2
    return q[n - m - 1]


def __no_repeated_digits(n):
    return '0' not in str(n) and all((c1 != c2 for (c1, c2) in combinations(str(n), 2)))


def __consistent(n, m, bulls, cows):
    bc, cc, n, m = 0, 0, str(n), str(m)
    for (c1, c2) in zip(n, m):
        if c1 == c2:
            bc += 1
        elif c2 in n:
            cc += 1
    return bc == bulls and cc == cows


def bulls_and_cows(guesses):
    possible = [n for n in range(1000, 10000) if __no_repeated_digits(n)]
    for (guess, bulls, cows) in guesses:
        possible = [x for x in possible if __consistent(x, guess, bulls, cows)]
    return possible


def count_consecutive_summers(n):
    i, j, summer_count, curr = 1, 1, 0, 1
    while j <= n:
        if curr == n:
            summer_count += 1
        if curr <= n:
            j += 1
            curr += j
        else:
            curr -= i
            i += 1
            if i > j:
                j = i
    return summer_count


def domino_cycle(tiles):
    prev = tiles[-1] if len(tiles) > 0 else None
    for tile in tiles:
        if prev[1] != tile[0]:
            return False
        prev = tile
    return True


def van_eck(n):
    seen, prev = dict(), 0
    for i in range(1, n + 1):
        if prev not in seen:
            seen[prev] = i - 1
            prev = 0
        else:
            curr = seen[prev]
            seen[prev] = i - 1
            prev = i - 1 - curr
    return prev
