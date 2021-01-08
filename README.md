# 109 Python Problems for CCPS 109

This repository contains the problem specifications and the automated tester for the graded lab problems for the course *CCPS 109 Computer Science I*, as taught by [Ilkka Kokkarinen](http://www.scs.ryerson.ca/~ikokkari/) for the Chang School of Continuing Education, Ryerson University, Toronto, Canada.

Write all your functions one by one into the same file `labs109.py` so that the automated tester script `tester109.py` can find them. The tester script will then test only those functions that you have implemented so far, and run the tests in order that your functions appear in the file.

Each function is tested by giving it a large number of pseudorandomly generated arguments, and a checksum of all answers is compared to the checksum produced by the instructor's private model solution. This allows the students to work at home and check at any time of their convenience whether their function is correct, without the need to release the private model solutions to the public. To help students debug their functions that do not pass the test, the file `expected_answers` contains the expected results for the first 300 test cases for each problem. The tester script will compare these expected results to the results produced by the student solution. In case of discrepancy, that particular test is terminated, and the test case arguments, expected correct result and the actual failing result are reported as a valuable aid to debugging.

Everyone who wishes to teach or learn Python is welcome to use, adapt and distribute these problems for their own purposes as they see fit. The author welcomes feedback by email at `ilkka.kokkarinen@gmail.com` from computer science instructors who use these problems in their courses.

The lab specification document and the automated tester software `tester109.py` are released under the [GNU General Public License v3](https://www.gnu.org/licenses/gpl-3.0.txt), with no warranties implied by the author.

Wordlist `words_sorted.txt` adapted from [dwyl/english-words](https://github.com/dwyl/english-words).
