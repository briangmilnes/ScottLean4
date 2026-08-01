% Code extracted from:
%   Fred Mesnard, Étienne Payet, Wim Vanhoof,
%   "Case study: proving sqrt(2) irrational with LPTP and an LLM",
%   ICLP 2026, EPTCS 450, pp. 67-80. doi:10.4204/EPTCS.450.5
%   arXiv:2607.21187  (CC-BY)
%
% NOTE: this arXiv paper is about LPTP (Logic Program Theorem Prover) and
% Prolog, NOT Lean. The pure logic program below is extracted verbatim from
% the paper. The paper's LPTP *proofs* are shown only as pretty-printed PDF
% renderings (with math notation), so they are not transcribed here as runnable
% LPTP source. The authors' full code and proofs are at:
%   https://github.com/FredMesnard/LPTP-LLM.git
%
% Natural numbers are terms built from the constant 0 and the function s/1.
% Predicates nat/1, plus/3, times/3, gcd/3, gcd_leq/3 come from the LPTP
% libraries `nat` and `gcd`.

even(0).
even(s(s(X))) :- even(X).

odd(s(0)).
odd(s(s(X))) :- odd(X).

nat(0).
nat(s(X)) :- nat(X).

leq(0, X).
leq(s(X), s(Y)) :- leq(X, Y).

plus(0, Y, Y).
plus(s(X), Y, s(Z)) :- plus(X, Y, Z).

times(0, Y, 0).
times(s(X), Y, Z) :- times(X, Y, P), plus(P, Y, Z).

gcd(X, Y, D) :-
    ( leq(X, Y) -> gcd_leq(X, Y, D)
    ; gcd_leq(Y, X, D) ).

gcd_leq(X, Y, D) :-
    ( X = 0 -> D = Y
    ; plus(X, Z, Y), gcd(X, Z, D) ).

% The question "are there coprime p, q with (p/q)^2 = 2, i.e. p^2 = 2q^2 ?"
% corresponds to this query (backtracking fairly explores N x N). The answer
% is no, but the search space is infinite so no LP engine returns a negative
% answer — hence the LPTP proof.
%
%   ?- nat(S), plus(P,Q,S), gcd(P,Q,s(0)),
%      times(P,P,P2), times(Q,Q,Q2), plus(Q2,Q2,P2).

% Section 5 wraps that same query in a rule, to prove operationally (with
% LPTP, in Claude Code / Opus 4.6 Code mode) that it cannot succeed:
sqrt2_is_rational :-
    nat(S), plus(P, Q, S), gcd(P, Q, s(0)),
    times(P, P, P2), times(Q, Q, Q2), plus(Q2, Q2, P2).

% ---------------------------------------------------------------------------
% Raw LPTP statement syntax, the one verbatim example given in the paper
% (a lemma whose proof is left as a gap placeholder, `ff by gap`):
%
%   :- lemma(sqr2:4, square(s(s(0))) = s(s(s(s(0)))), ff by gap).
