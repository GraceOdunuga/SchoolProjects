% CISC 360 a4, Fall 2023
%
% See a4.pdf for instructions

/*
 * Replace  this is a syntax error  with your student ID number:
 */
student_id(20292380).
% second_student_id(  ).
% If in a group, uncomment the second_student_id line
%   and put the second student's ID between the ( )
check_that_you_added_your_student_id_above().


/*
 * Q1: Prime numbers
 */

/*
  factors_loop(N, Start, Factors):
      Given integers N > 1 and Start > 1,
          return in Factors a list of all F such that
                 (F >= Start)
             and F < N
             and (N mod F) = 0.

  This predicate is already used within `factors`.
  You probably don't need to call `factors_loop` yourself.
*/
factors_loop( N, Start, []) :- N > 1, Start > 1, Start >= N.

factors_loop( N, Start, [Start | Rest]) :-
      N > 1, Start > 1, Start < N,
      (N mod Start) =:= 0,
      Next is Start + 1,
      factors_loop( N, Next, Rest).

factors_loop( N, Start, Rest) :-
      N > 1, Start > 1, Start < N,
      (N mod Start) =\= 0,
      Next is Start + 1,
      factors_loop( N, Next, Rest).

/*
  factors(N, Factors): Given an integer N > 1,
                          return in Factors a list of all F such that
                              F > 1 and F < N and (N mod F) = 0.
                       (The list Factors includes non-prime factors.
                        For example, factors(20, [2, 4, 5, 10]) is true.)
*/
factors(N, Factors) :- N > 1, factors_loop( N, 2, Factors).

/*
  Q1a.

  is_prime(N, Answer)

  Given an integer N >= 2:
    Answer = prime               iff  N is prime
    Answer = composite(Factors)  iff  N is not prime, with *prime* factors Factors

  Examples:
      ?- is_prime(11, Answer).
    Answer = prime
    ?- is_prime(20, Answer).
    Answer = composite([2, 5])    % The factors of 20 are: 2, 4, 5, 10.
                                  % The *prime* factors of 20 are: 2, 5.

   Replace the word "change_this" in the second rule below.
   
   Hint: You should return the *prime* factors (not all of the factors),
         but it may be useful to first write a version of is_prime
           that returns all of the factors,
         complete question Q1b,
         and then return to this question.
*/

is_prime(N, prime) :-
    factors(N, []).
    
is_prime(N, composite(PrimeFactors)) :-
    /* Hint: our code for is_prime(N, prime) :-  checks if N has no factors.
             Here, check if N has at least one factor.
       Hint: You can use  List \= []  to check if List is not empty.
    */
    factors(N, FactrsList), 
    FactrsList \= [],
    find_primes(FactrsList, PrimeFactors).

/*
  find_primes(Numbers, Primes)
    Primes = list of N in Numbers such that N is prime,
             in the same order as Numbers.

  Return only one solution.

  For example,

   ?- find_primes([2, 3, 4, 5, 6, 7, 8], Primes).
   Primes = [2, 3, 5, 7] ;
   false.
 
  Q1b. Replace the word "change_this" in the rules below.
       Hint:  Try to use  find_primes(Xs, Ys).
*/
find_primes([], []).

/*
  In this rule, we include X in the output: [X | Ys].
  So this rule should check that X is prime.
*/
find_primes([X | Xs], [X | Ys]) :-
  is_prime(X, prime),
  find_primes(Xs, Ys).

/*
  In this rule, we do not include X in the output: Ys.
  So this rule should check that X is not prime.
*/
find_primes([X | Xs], Ys) :-
  not(is_prime(X, prime)),
  find_primes(Xs, Ys).


/*
  upto(X, Y, Zs):
  Zs is every integer from X to Y

  Example:
     ?- upto(3, 7, Range)
     Range = [3, 4, 5, 6, 7]
*/
upto(X, X, [X]).
upto(X, Y, [X | Zs]) :-
    X < Y,
    Xplus1 is X + 1,
    upto(Xplus1, Y, Zs).

/*
  primes_list(M, N, Primes)
    Primes = all prime numbers between M and N, in increasing order.
    Example:
      ?- primes_list(60, 80, Primes).
      Primes = [61, 67, 71, 73, 79] .

 (Return only one solution.)

 Q1c. Replace the word "change_this" in the rule below.
      HINT: Use upto and find_primes.
*/

primes_list(M, N, Primes) :-
  upto(M, N, RangeList),
  find_primes(RangeList, Primes).



/*
 * Q2. Translate the spiral function from Assignment 1:
 *
  `spiral': given two integers `dir' and `span',
  returns 1 if `dir' is less than or equal to 0,
  and otherwise returns (span - dir) * spiral (span - dir) (span - 4).

  Here is a Haskell solution:
  
    spiral :: Integer -> Integer -> Integer
    spiral dir span = if dir <= 0 then 1
                      else (span - dir) * spiral (span - dir) (span - 4)

  Write a Prolog predicate

    spiral

  such that  spiral(Dir, Span, R) is true  iff  R = (spiral Dir Span)
                                                (in Haskell)

  Hint: It may be useful to rewrite 'spiral' using 'let' and/or 'where'.

  We have written one clause, corresponding to the "then" part of
  the Haskell function, for you.
*/

%returns 1 if `dir' is less than or equal to 0,
spiral(Dir, _, 1) :- Dir =< 0.
%else:
spiral(Dir, Span, R) :-
    Num1 is Span - Dir,
    Num2 is Span - 4,
    spiral(Num1, Num2, R2),
    R is Num1 * R2.

/*
  To test: ?- spiral(0, 32, 1).
           true ;                % type ;
           false.
           ?- spiral(-32, 5, 1).
           true ;                % type ;
           false.
           ?- spiral(13, 3, R).
           R = -10 .             % type .
           ?- spiral(7, 6000, R).
           R = -107676231;       % type ;
           false.

  Hint: The last query (and similar queries) should give
        only one solution.
*/


/*
  Q3: Trees

  Consider the tree     (We are *not* representing
                          trees with Empty "leaves":
             4                         4
            / \                      /   \
           2   5                   2       5
          / \                    /  \     / \
         1   3                 1     3   E   E
                              / \   / \
                          Empty  E E   E            )
                 
  We will express the above tree in Prolog as

    node( 4, node( 2, leaf(1), leaf(3)), leaf(5))
  
  This kind of tree is similar to this Haskell type:
  
    data A4Tree = Node Integer A4Tree A4Tree
                | Leaf Integer

  In this question, a  key at level L  is a key that appears at level L of the tree,
  counting the root as level 0, the root's children as level 1, and so on.

  For example, in the tree

                         4          Level 0
                        / \      
                       2   5        Level 1
                      / \        
                     1   3          Level 2

  the key 4 is at level 0, the keys 2 and 5 are at level 1, and the keys 1 and 3 are at level 2.

  In this question, define a Prolog predicate

    atlevel(L, T, K)

  that is true iff key K appears at level L of tree T.

  For example:
  
    ?- atlevel( 0, node(2, leaf(1), leaf(3)), 2).
    true

    ?- atlevel( 1, node( 4, node( 2, leaf(1), leaf(3)), leaf(5)), 5).
    true

  Your predicate should be written so that when the first argument is a specific integer
  (like 0, 1, etc.), the second argument is a specific tree (containing no variables),
  and the third argument is a variable,
  typing ; returns *all* keys at that level in the tree.
  For example:

    ?- atlevel( 1, node( 4, node( 2, leaf(1), leaf(3)), leaf(5)), Key).
    Key = 2 ;
    Key = 5 ;
    false

    (Also acceptable:
    ?- atlevel( 1, node( 4, node( 2, leaf(1), leaf(3)), leaf(5)), Key).
    Key = 2 ;
    Key = 5. )

  If the level "goes below" the tree, atlevel should be false.
  For example, the tree  leaf(1000)  has only level 0:

    ?- atlevel( 1, leaf(1000), K).
    false

  Define clauses for 'atlevel' below.
*/

%If the level 0 then there is only one key wich is the root of the tree 
atlevel(0, node(Key, _, _), Key).

% If the level is 1 and the current node is a leaf, check if the leaf contains the desired key.
atlevel(0, leaf(Key), Key).

% If the level is greater than 1 and the left subtree is a node, recursively search the left subtree.
atlevel(Level, node(_, Left, _), Key) :-
    Level > 0,
    NewLevel is Level - 1,
    atlevel(NewLevel, Left, Key).

% If the level is greater than 1 and the right subtree is a node, recursively search the right subtree.
atlevel(Level, node(_, _, Right), Key) :-
    Level > 0,
    NewLevel is Level - 1,
    atlevel(NewLevel, Right, Key).

%testing
% simple_tree(node(1, node(2, leaf(4), leaf(5)), leaf(3))).
% deeper_tree(node(10, node(20, leaf(40), leaf(50)), node(30, leaf(60), leaf(70)))).
