Runs against teorth/expdb (commit c8eda5e, 2026-09-26), in an isolated venv (python 3.13, pycddlib 2.1.8).
Setup: clone; python -m venv; pip install -r blueprint/src/python/requirements.txt (needs brew cddlib gmp); tests/test_all.py passed.
- zlv_term.py: isolates sup_{tau in [2,tau0]} LV_zeta(sigma,tau)/tau (Cor. 11.7 second term) on [0.7, 7/8] with and without the
  quasi-RH mu points (mu(7/8)=0 and convexity points). RESULT: identical with and without, for tau0 = 3 and 5 (2026-10-27).
  Hence the engine's mu -> zeta-large-value conversion (single-point, Cor. 8.13 type) yields no zero-density gain below 7/8.
- targeted.py / exp_78.py: fuller searches (killed after 25 min / 80 min; redundant once zlv_term.py was decisive).
