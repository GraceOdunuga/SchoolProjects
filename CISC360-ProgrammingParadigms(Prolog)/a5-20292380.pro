%
% CISC 360
% Assignment 5
% Fall 2023
%

/*
 * Student ID
 */
student_id(20292380).
% second_student_id(  ).
% if in a group, uncomment the  second_student_id  line and put the other student ID there

/*
  In this version of classical propositional logic,
  we have the following possible Formulas:

  top                        % truth
  bot                        % falsehood
  and(Formula, Formula)      % conjunction
  or(Formula, Formula)       % disjunction`
  implies(Formula, Formula)  % implication
  not(Formula)               % negation
  v(PropVar)                 % atomic propositions (Atom(...) in a3)

  Some example atomic formulas:

    v(a)
    v(b)
    v(c)
    v(d)
    v(e)
*/

/*
Q1: Even and Odd

In this question, a literal is a variable (atomic proposition).
For example:

   v(c)       v(a)       v(aratherlongword)

are literals.

A formula psi is "odd" iff every literal in psi appears below an *odd*
number of negations, where:

   not(P)         is a negation for P

   implies(L, R)  is a negation for L  (but isn't a negation for R!)

For example, consider the formula

   and(not(v(a)),
       implies(v(b), v(c)))

whose parse tree is

       and        
      /   \       
   not     implies                
    |       /    \
   v(a)  v(b)   v(c)

The literal v(a) appears below a 'not', so it appears under 1 negation.
The literal v(b) is the *left* child of an 'implies', so it appears under 1 negation.
The literal v(c) is the *right* child of an 'implies', so it appears under 0 negations.

This formula is not "odd" because v(c) appears under 0 negations, and 0 isn't an odd number.

Here is a formula that *is* odd:

    implies( v(a), not(implies(bot, v(b))))

then its parse tree is

      implies
      /   \
   v(a)    not
            |
         implies
          /   \  
        bot    v(b)

in which v(a) appears under 1 negation, and
         v(b) appears under 1 negation (1 for the 'not')
         .
Since 1 is an odd number, the formula  implies( v(a), not(implies(bot, v(b))))  is odd.

Q1.
Write a Prolog predicate oddliterals( Phi) that, given a concrete formula Phi,
is true iff Phi is odd.

Your predicate should work for formulas that involve any combination of
'top', 'bot', 'v(...)', 'not', 'and', and 'implies'.

Your predicate doesn't have to work for 'or' (the code would be identical to the code for
'and', so you wouldn't learn anything more by doing that).

Hint 1: In Prolog, to check that X is odd, you could use a premise  X mod 1 =:= 0

Hint 2: You may need to write a 'helper predicate' that takes an extra argument:

    oddhelper( N, Phi)

Here N could be the number of negations seen so far.  For example, the query

   ?- oddliterals(not(v(a))).

should be true (v(a) appears under 1 negation, and 1 is odd),
so you might want to call  oddhelper( 1, v(a)).

Other approaches may be possible, but your instructor doesn't see a way to solve
this question without using a helper predicate of some kind.
*/

oddhelper(N, v(_)) :- N mod 2 =:= 1. % Check if N is odd for literals

oddhelper(N, not(Phi)) :- oddhelper(N + 1, Phi).
oddhelper(N, and(Phi1, Phi2)) :-  oddhelper(N, Phi1), 
                                  oddhelper(N, Phi2).
oddhelper(N, implies(Phi1, Phi2)) :-  oddhelper(N + 1, Phi1), 
                                      oddhelper(N, Phi2).
oddhelper(_, top).
oddhelper(_, bot).

oddliterals(Phi) :- oddhelper(0, Phi).






/*
Q2: Tiny Theorem Prover
*/


/*
  prove(Ctx, P, Deriv):
    true if, assuming everything in Ctx is true,
     the formula p is true according to the rules given in a5.pdf,
     where Deriv represents the rules used.
     
  This is the cool part:
  *each rule can be implemented with a single Prolog clause*.

  There is no "problem solving" where someone (like the instructor)
  figures out a strategy for applying -Left and -Right rules without getting
  into an infinite loop.

  We don't need to deal with continuations or with implementing
  backtracking search for all possible proofs (as we had to for a3):
  Prolog always does backtracking search.

  (Because we want to do backtracking search, it seems unlikely
  that cuts will be useful in this part of the assignment.)
*/

/*                          P in Ctx
                          ––––––––––––
 rule 'UseAssumption'       Ctx |- P
*/
prove( Ctx, P, use_assumption(P)) :- member( P, Ctx).

/*                       ––––––––––
  rule 'Top-Right'       Ctx |- top
*/
prove( _,   top, top_right).

/*
  We will use append "backwards":
  instead of taking concrete lists
  provided in a query, we take a concrete *appended* list Ctx
  and use append to "split up" the Ctx.
*/

/*
Q3a:
  Write Prolog clauses that correspond to the rules

    And-Right,
    Implies-Right.
*/

/*
  rule 'And-Right'
               Ctx |- Q1     Ctx |- Q2
               -----------------------
  CONCLUSION:    Ctx |- and(Q1, Q2)

  Put the result of prove on Ctx |- Q1 into Deriv1,
  and the result of prove on Ctx |- Q2 into Deriv2.
*/
prove(Ctx, and(Q1, Q2), and_right(Deriv1, Deriv2)) :- prove(Ctx, Q1, Deriv1),
                                                      prove(Ctx, Q2, Deriv2).



/*
  rule 'Implies-Right'
                  [P | Ctx] |- Q
               -------------------------
  CONCLUSION:     Ctx |- implies(P, Q)

  Put the result of prove on [P | Ctx] |- Q into Deriv,
  and return implies_right(Deriv).
*/
prove(Ctx, implies(P, Q), implies_right(Deriv)) :- prove([P | Ctx], Q, Deriv).




/*
  rule 'And-Left'
                          CtxP12
                 vvvvvvvvvvvvvvvvvvvvvvvv
                 Ctx1 ++ [P1, P2] ++ Ctx2 |- Q
               ----------------------------------
  CONCLUSION:  Ctx1 ++ [and(P1, P2)] ++ Ctx2 |- Q
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^    ^
               1st argument to prove            2nd argument to prove
*/
prove( Ctx, Q, and_left(Deriv)) :-

  append( Ctx1, [and(P1, P2) | Ctx2], Ctx),    %  Ctx1 ++ [and(P1, P2) | Ctx2]  ==  Ctx
  
  append( Ctx1, [P1 | [P2 | Ctx2]], CtxP12),   %  Ctx1 ++ [P1 | [P2 | Ctx2]]    ==  CtxP12
  
  prove( CtxP12, Q, Deriv).


/*
  Q3b: Implies-Left
*/

/*
  rule 'Implies-Left'
               Ctx1 ++ Ctx2 |- P1     Ctx1 ++ [P2] ++ Ctx2 |- Q
               ------------------------------------------------
   CONCLUSION:     Ctx1 ++ [implies(P1, P2)] ++ Ctx2 |- Q

   In the third argument, return implies_left(Deriv1, Deriv2)
     where Deriv1 is produced by calling prove on P1,
     and Deriv2 is produced by calling prove on Q.
*/
prove(Ctx, Q, implies_left(Deriv1, Deriv2)) :-  append(Ctx1, [implies(P1, P2) | Ctx2], Ctx),
                                                append(Ctx1, Ctx2, CtxP1),
                                                prove(CtxP1, P1, Deriv1),
                                                append(Ctx1, [P2 | Ctx2], CtxP2),
                                                prove(CtxP2, Q, Deriv2).



/* Q3c, Q3d, Q3e: Bot-Left, Not-Left, Not-Right

   Refer to the rules in a5.pdf, constructing the derivations (third argument) as indicated below.
*/

/* Q3c: Bot-Left   Return bot_left in the third argument.
*/
prove(Ctx, Q, bot_left) :- append(Ctx1, [bot | Ctx2], Ctx).


/* Q3d: Not-Left   In the third argument,
                   return not_left(Deriv)
                   where Deriv was produced by the premise Ctx1 ++ Ctx2 |- P.
*/
prove(Ctx, bot, not_left(Deriv)) :- append(Ctx1, [not(P) | Ctx2], Ctx),
                                    append(Ctx1, Ctx2, CtxP),
                                    prove(CtxP, P, Deriv).


/* Q3e: Not-Right  In the third argument,
                   return not_right(Deriv)
                   where Deriv was produced by the premise [P | Ctx] |- bot.
*/
prove(Ctx, not(P), not_right(Deriv)) :- prove([P | Ctx], bot, Deriv).




/*
  ?- prove([implies(v(b), v(h))], implies(v(b), v(h)), Deriv).
  Deriv = use_assumption(implies(v(b), v(h))) ;
   % CISC 204-style proof:
   %    1. implies(v(b), v(h))     premise       use_assumption
   %
   
  Deriv = implies_right(implies_left(use_assumption(v(b)), use_assumption(v(h)))) ;
   % CISC 204-style proof:
   %     ____________________________________
   % 1  | v(b)                    assumption |   use_assumption(v(b))
   % 2  | implies(v(b), v(h))     premise    |
   % 3  | v(h)                    ->e 2, 1   |   use_assumption(v(h)) + implies_left
   %    |____________________________________|
   % 4   implies(v(b), v(h))      ->i 1-3        implies_right]
   %
   
  false.

  ?- prove([v(d)], implies(and(v(b), v(b)), v(d)), Deriv).
  Deriv = implies_right(use_assumption(v(d))) ;
  Deriv = implies_right(and_left(use_assumption(v(d)))) ;
  false.

  ?- prove([implies(and(v(b), v(e)), v(d))], implies(v(b), v(h)), Deriv).
  false.

  ?- prove([and(and(v(a), v(b)), and(v(d), (v(e))))], v(d), Deriv).
  Deriv = and_left(and_left(and_left(use_assumption(v(d))))) ;
  Deriv = and_left(and_left(use_assumption(v(d)))) ;
  Deriv = and_left(and_left(and_left(use_assumption(v(d))))) ;
  false.
*/




/*
  BONUS (up to 5%):
  Implement the Or-Left, Or-Right-1, Or-Right-2 rules from Assignment 3.
*/

