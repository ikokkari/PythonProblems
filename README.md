# 109 Python Problems for CCPS 109

This repository contains the problem specifications, the automated tester and the necessary data files for the graded lab problems for the course *CCPS 109 Computer Science I*, as taught by [Ilkka Kokkarinen](http://www.scs.ryerson.ca/~ikokkari/) for the Chang School of Continuing Education, Ryerson University, Toronto, Canada.

Write all your functions one by one into the same file `labs109.py` so that the tester script `tester109.py` can find them. When run, this tester will execute the tests precisely for the functions implemented so far in `labs109.py`. The tests are executed in the same order that your functions appear in that file.

Each function is given a large number of pseudorandomly generated arguments. A checksum is computed for the returned answers, and this checksum is compared to the checksum computed from the instructor's private model solution. The lab solution is accepted if and only if these two checksums are identical and the function runs in a reasonable time. This whole setup allows students to work at home and check at any convenient time whether their function is correct. This eliminates any need for additional labour by the the human instructor or the TA's. Once students have given each problem a good old "college try" and haven't been able to untangle that knot, they can contact the course personnel for help to get them untangled. 

In addition to these precomputed checksums that determine the acceptance of each function, the file `expected_answers` contains the expected results for the first 300 test cases for each problem. The tester will compare these in lockstep to the results produced by the student solution. At the first discrepancy, that particular test is immediately terminated, and the test case arguments, the expected correct result and the returned incorrect result are displayed as a valuable aid to debugging. Having a reasonably short but explicit test case available is an invaluable aid in debugging a function that does not pass the automated test.

Everyone teaching or learning Python is welcome to use, adapt and distribute these problems for their own purposes as they see fit. The author welcomes feedback by email at `ilkka.kokkarinen@gmail.com` from computer science instructors who use these problems in their courses.

The lab specification document and the automated tester software `tester109.py` are released under the [GNU General Public License v3](https://www.gnu.org/licenses/gpl-3.0.txt), with no warranties implied by the author.

Wordlist `words_sorted.txt` adapted from [dwyl/english-words](https://github.com/dwyl/english-words).
