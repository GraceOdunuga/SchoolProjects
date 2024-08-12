-- CISC 360 a3, Fall 2023

-- SEE THE FILE a3.pdf
-- for instructions

module A3
where
import Data.List

-- Rename this file to include your student ID: a3-studentid.hs
-- Also, add your student ID number after the "=":
student_id :: Integer
student_id = 20292380

{- If you are working in a group of 2, uncomment the line below and add the second student's ID number: -}
second_student_id = 20282229
{- If you are working in a group of 2, uncomment the line above. -}


-- THIS FILE WILL NOT COMPILE UNTIL YOU ADD YOUR STUDENT ID ABOVE
check_that_you_added_your_student_ID_above = ()


-- Variable is a synonym for String.
type Variable = String

-- In our simplified version of classical propositional logic,
-- we have the following definition for a Formula:
data Formula = Top                      -- truth (always true)
             | Bot                      -- falsehood (contradiction)
             | And Formula Formula      -- conjunction
             | Or Formula Formula       -- disjunction
             | Implies Formula Formula  -- implication
             | Not Formula              -- negation
             | Atom Variable            -- atomic proposition ("propositional variable")
             deriving (Eq, Show)

-- Some atoms, for convenience
vA = Atom "A"
vB = Atom "B"
vC = Atom "C"
vD = Atom "D"
vE = Atom "E"
vF = Atom "F"
vp = Atom "p"
vq = Atom "q"

-- Some example formulas that you can use to test your functions
formula1  = Implies (And vA vB) vC
formula2  = Implies Bot (And vA vB)
formula3  = Implies (And vA vB) Top
formula4  = And (Implies vA (And vB vC)) (And vD vE)
formula5  = And vA vB
formula6  = Not vA
formula7  = Implies vA vB
formula8  = Or vA (Not vA)
formula9  = Or vA (Not vB)


{-
Q1: Horn clauses

Write a function that tells us whether a given formula is a *fact* (a single positive literal)
or a *rule* (an implication whose antecedent is a conjunction of positive literals, and whose conclusion is a positive literal).

   1. Positive literals:
      an Atom is a *positive literal*.

   2. Conjunctions of positive literals:
  
       - a positive literal is a *conjunction of positive literals*;
       - an And of conjunctions of positive literals
         is a *conjunction of positive literals*.

      For example, Atom "X" is a positive literal, so it is a conjunction of positive literals.
      And (Atom "B") (Atom "C") is an And of positive literals, so it is a conjunction of positive literals.
      And (And (Atom "B") (Atom "C")) (Atom "D") is a conjunction of positive literals.

   3. Facts:
      a positive literal is a *fact*.

   4. Rules:
      an implication (Implies formula1 formula2) is a *rule* iff formula1 is a conjunction of positive literals, and formula2 is a positive literal.
      
If you're familiar with grammars, the above definitions can also be expressed as:

   <pos-lit> ::= Atom <string>

   <conj>    ::= <pos-lit>
               | And <conj> <conj>

   <fact>    ::= <pos-lit>

   <rule>    ::= Implies <conj> <pos-lit>
-}
data FormulaKind = Fact | Rule | NotClause
                   deriving (Show, Eq)

{- Q1a: 'classify'

Write a function

   classify :: Formula -> FormulaKind

that takes a Formula, and returns:

     Fact       if the formula is a fact
     Rule       if the formula is a rule
     NotClause  if the formula is neither a fact nor a rule 

You will probably need to write at least one helper function.
-}
classify :: Formula -> FormulaKind
classify (Atom _)                             = Fact
classify (Implies antecedent consequent)      = if conj_of_lits (antecedent) == True && pos_lit consequent
                                                then Rule
                                                else NotClause
classify (_)                                  = NotClause

pos_lit :: Formula -> Bool
pos_lit (Atom _) = True
pos_lit (_) = False

conj_of_lits :: Formula -> Bool
conj_of_lits (Atom _)  = True
conj_of_lits (And a b) = if conj_of_lits a && conj_of_lits b
                         then True 
                         else False 
conj_of_lits (_)       = False

{- Q1b: test cases

Write test cases that completely "cover" the input, output, and code
of 'classify'.  See a3.pdf.
-}
test_classify1 :: Bool
test_classify1 = (classify (Atom "T") == Fact)
{- add your test cases here: -}

-- Rule with And in the antecedent
test_classify2 :: Bool
test_classify2 = (classify (Implies (And (Atom "A") (Atom "B")) (Atom "C")) == Rule)

-- Simple Rule
test_classify3 :: Bool
test_classify3 = (classify (Implies (Atom "A") (Atom "B")) == Rule)

-- Combination that is neither Fact nor Rule
test_classify4 :: Bool
test_classify4 = (classify (And (Atom "X") (Atom "Y")) == NotClause)

-- Complex Combination that is neither Fact nor Rule
test_classify5 :: Bool
test_classify5 = (classify (And (Atom "X") (And (Atom "Y") (Atom "Z"))) == NotClause)

-- Test a deeply nested Rule with multiple Ands
test_classify8 :: Bool
test_classify8 = (classify (Implies (And (Atom "A") (And (Atom "B") (Atom "C"))) (Atom "D")) == Rule)

-- Test a large combination of Ands, which is neither Fact nor Rule
test_classify9 :: Bool
test_classify9 = (classify (And (Atom "A") (And (Atom "B") (And (Atom "C") (And (Atom "D") (Atom "E"))))) == NotClause)

-- Empty input, which should result in NotClause
test_classify10 :: Bool
test_classify10= (classify (Atom "") == Fact)

-- Test conjunction of Ands as the consequent
test_classify11 :: Bool
test_classify11 = (classify (Implies (Atom "Z") (And (Atom "X") (Atom "Y")) ) == NotClause)

-- Test random argument of type Formula (Top)
test_classify12 :: Bool
test_classify12 = (classify (Top) == NotClause)

test_classify :: Bool
test_classify = all (\x -> x) [test_classify1,
                              test_classify2,
                              test_classify3,
                              test_classify4,
                              test_classify5,
                              test_classify8,
                              test_classify9,
                              test_classify10,
                              test_classify11,
                              test_classify12
                               ] --           ^ add your test cases here
{- The library function 'all' applies its first argument to each element in the list,
   and returns True iff the first argument returns True every time. -}



{-
Q2: Truth Tables

To build a truth table for a formula, there are 4 steps:

  1) Traverse the formula to find all atomic propositions (propositional variables).

  2) Find all the possible valuations---combinations of True and False
      for the atomic propositions in the formula.

  3) Evaluate the formula for each valuation obtained in (2).

  4) Use the results of (1-3) to build the table.

In this question, you will implement steps (1-3).
-}


-- A Valuation is a list of pairs corresponding to a truth value (i.e. True or False)
--  for each atom in a formula
type Valuation = [(Variable, Bool)]

-- A TruthTable is an enumeration of the valuations for a given formula,
-- with each valuation paired with the corresponding evaluation of that formula.
-- (This corresponds to a truth table with no "intermediate columns".)
data TruthTable = TruthTable [(Valuation, Bool)]

{-
   This function is here so that when you print a TruthTable in GHCi, the table is nice and readable.
   You don't need to understand how this works to complete the assignment.
-}
instance Show TruthTable where
  show (TruthTable rows) =
    case rows of
      [] -> ""
      ([], result) : _ -> "   result is " ++ pad_show result ++ "\n"
      ((c,b) : valu, result) : xs -> 
        c ++ "=" ++ (pad_show b) ++ "   "
          ++ show (TruthTable [(valu,result)])
          ++ show (TruthTable xs)
    where
      pad_show True  = "True "
      pad_show False = "False"

{-
  Q2a: getVariables:

  Traverse a formula and build a list of all Variables in the formula, without duplicates.

  You may use the built-in function "nub", which takes a list and returns the list
  without duplicates.
-}
getVariables :: Formula -> [Variable]

getVariables Top               = []
getVariables Bot               = []

getVariables (Atom v)          = [v]

getVariables (Not phi)         = getVariables phi
getVariables (And phi1 phi2)   = nub (getVariables phi1 ++ getVariables phi2)
getVariables (Or phi1 phi2)    = nub (getVariables phi1 ++ getVariables phi2)
getVariables (Implies phi psi) = nub (getVariables phi ++ getVariables psi)

{-
   Q2b: getValuations:

   Build a list of all possible valuations for a set of atomic propositions
-}
getValuations :: [Variable] -> [Valuation]
getValuations []       = [[]]
getValuations (c : cs) = map (\val -> (c, True) : val) rest 
                      ++ map (\val -> (c, False) : val) rest
                      where  rest = getValuations cs
{-
  Hint: To apply a function f to every element of a list xs,
   write  map f xs.
  For example, the following adds 1 to the start of every list
   in a list of lists [[2,3], [2,4]]:
   map (\ys -> 1 : ys) [[2,3], [2,4]]  ==  [[1,2,3], [1,2,4]]
-}

{-
   Q2c: evalF:
    Evaluate a formula with a particular valuation,
     returning the resulting boolean value
-}
evalF :: Valuation -> Formula -> Bool
evalF valu formula =
    case formula of
        Top               -> True
        Bot               -> False
        Not phi1          -> not (evalF valu phi1)
        Implies phi1 phi2 -> not (evalF valu phi1) || (evalF valu phi2)
        Atom c            -> case lookup c valu of
                             Just q  -> q  -- c was found, q is its associated value
                             Nothing -> error "unknown variable in valuation"  -- c was not found
        And phi1 phi2     -> evalF valu phi1 && evalF valu phi2
        Or phi1 phi2      -> evalF valu phi1 || evalF valu phi2

-- buildTable:
--  Build a truth table for a given formula.
--  You can use this function to help check your definitions
--  of getVariables, getValuations and evalF.
buildTable :: Formula -> TruthTable
buildTable psi =
  let valuations = getValuations (getVariables psi)
  in
    TruthTable (zip valuations
                    (map (\valu -> evalF valu psi) valuations))

--testing 
sampleFormula :: Formula
sampleFormula = And (Atom "p") (Atom "q")


{-
Q3: Tiny Theorem Prover

    This question asks you to complete an implementation of a
    continuation-based backtracking theorem prover that follows the rules
    given in a3.pdf.
 
    The prover is structured using two functions that do all the work,
    and one function that "kicks off" the process by passing continuations:

       prove_core  looks at the goal formula (the formula we're trying to prove),
                     trying the -Right rules;
 
       prove_left  looks at the assumptions, trying the -Left rules;

       prove_all   calls prove_core, collecting all solutions.

    [X] Use-Assumption
    [ ] Top-Right
    [X] Implies-Right
    [X] And-Right
    [ ] Or-Right-1 and Or-Right-2
    
    [X] Bot-Left
    [X] Implies-Left
    [ ] And-Left
    [ ] Or-Left
-}

-- a Context is a list of Formulas, representing assumptions
type Context = [Formula]

{- A Derivation represents the rules used to construct a proof.

   For example, if we prove

    [vB] |- (And vB Top)
     
   by using UseAssumption to prove vB, TopRight to prove Top, and then AndRight,
   the Derivation would be

     AndRight (UseAssumption vB) TopRight

   As a tree, drawn the way computer scientists usually draw it, this looks like

               AndRight
              /        \
       UseAssumption   TopRight
            vB

   But it's easier to see the connection to the rules if we draw the root at the bottom:

            vB                        ---------- UseAssumption       ----------- TopRight
       UseAssumption   TopRight       [vB] |- vB                     [vB] |- Top
              \        /              --------------------------------------------------- AndRight
               AndRight                               [vB] |- And vB Top

The arguments to a Derivation constructor represent the premises used,
or for UseAssumption, the assumption formula being used.

OrRight takes an extra first argument indicating whether rule OrRight-1 or OrRight-2
was used.

For example,

   [OrRight 2 (UseAssumption vB)]

should be returned by

   prove_all [vB] (Or vA vB)

-}
data Derivation = UseAssumption Formula
                | TopRight
                | BotLeft
                | ImpliesRight Derivation
                | AndRight Derivation Derivation
                | ImpliesLeft Derivation Derivation
                | AndLeft Derivation
                | OrLeft Derivation Derivation
                | OrRight Int Derivation
                deriving (Show, Eq)

{-
  prove_core: Given a context, a formula, and two continuations representing success and failure,
          call the appropriate continuation.
-}
prove_core :: Context         -- formulas being assumed (to the left of the turnstile  |-  )
           -> Formula         -- goal formula to be proved (to the right of the turnstile)
           -> (Derivation -> (() -> b) -> b,
                              -- kSucceed: call this if we proved the formula,
                              --    with the constructed Derivation and a function to call to get more proofs
               () -> b)       -- kFail: call this if we can't prove the formula
           -> b

prove_core ctx goal (kSucceed, kFail) =
  let try_prove_left () = prove_left ctx ([], ctx) goal (kSucceed, kFail)
      try_right_rules () =
           case goal of
                Top              -> -- Top-Right rule
                     -- undefined                            --      ctx ⊢ Top              ⊤   by ⊤intro
                     -- we have succeeded
                     -- call kSucceed  ::  Derivation -> (() -> b) -> b
                     kSucceed TopRight try_prove_left

                     -- kSucceed TopRight (\() -> try_prove_left)   -- almost correct (please don't correct it right now)
                     


                Implies phi psi  -> -- Implies-Right rule
                     prove_core (phi : ctx)
                            psi
                            (\deriv -> \more ->
                                 kSucceed (ImpliesRight deriv) more,
                             try_prove_left)

                And phi1 phi2    -> -- And-Right rule
                     prove_core ctx phi1
                            (\deriv1 -> \more1 ->
                                 prove_core ctx phi2
                                      (\deriv2 -> \more2 ->
                                          kSucceed (AndRight deriv1 deriv2) more2,
                                       more1),
                                 try_prove_left)

                Or phi1 phi2     -> -- Or-Right rules (try Or-Right-1, if it fails, try Or-Right-2)
                    prove_core ctx phi1
                          (\deriv1 -> \more1 ->
                              kSucceed (OrRight 1 deriv1) more1,
                                        \() -> -- If Or-Right-1 fails, try Or-Right-2
                                          prove_core ctx phi2
                                                (\deriv2 -> \more2 ->
                                                    kSucceed (OrRight 2 deriv2) more2,
                                                    try_prove_left))
                                                    --kFail))
                _                 -> -- Can't use any of the -Right rules, so:
                                  try_prove_left ()
  in
    if elem goal ctx then  -- Use-Assumption rule
      kSucceed (UseAssumption goal) try_right_rules
    else
      try_right_rules ()

{-
  prove_left: Given an original context,
                    a context that prove_left has already processed,
                    a context that prove_left has not processed,
                    a goal formula,
                    and two continuations,
                    call the appropriate continuation.
-}
prove_left :: Context              -- the original context
           -> (Context, Context)   -- the "done" context, and the "to do" context
           -> Formula              -- the goal formula
           -> (Derivation -> (() -> b) -> b,            -- kSucceed: call this if we proved the formula
               () -> b)            -- kFail: call this if we can't prove the formula
           -> b
           
prove_left original (done, []) goal (kSucceed, kFail) =
                       --  ^^ the "to do" context is empty, so there's nothing remaining to examine
    if original == done then
        -- prove_left looked at everything but didn't change the context at all, so fail
        kFail ()
    else
        -- prove_left changed something, so we are giving prove_core stronger assumptions
        prove_core done goal (kSucceed, kFail)
        
prove_left original (done, focus : rest) goal (kSucceed, kFail) =

    let leave_alone () =   -- leave_alone: Call this to move "focus", the head of the to-do list,
                           --              into the "done" list without changing "focus"
            prove_left original (done ++ [focus], rest) goal (kSucceed, kFail)
    in
      case focus of
        Bot ->                -- Bot-Left rule
            kSucceed BotLeft leave_alone
            
        Implies phi1 phi2 ->  -- Implies-Left rule
            prove_core (done ++ rest) phi1 (-- kSucceed:
                                        \deriv1 -> \more1 ->
                                             prove_core (done ++ [phi2] ++ rest)
                                                    goal
                                                    (\deriv2 -> \more2 ->
                                                        kSucceed (ImpliesLeft deriv1 deriv2) more2,
                                                     more1),
                                        -- kFail:
                                        leave_alone)
 
        And phi1 phi2 ->      -- And-Left rule
            prove_core (done ++ [phi1, phi2] ++ rest) goal
              (-- kSucceed
                \deriv -> \more -> 
                  kSucceed (AndLeft deriv) more,
                  -- kFail
              leave_alone)
        
        Or phi1 phi2 ->       -- Or-Left rule
            prove_core (done ++ [phi1] ++ rest) phi1
                                      (-- kSucceed:
                                      \deriv1 -> \more1 ->
                                              prove_core (done ++ [phi2] ++ rest) goal
                                    (\deriv2 -> \more2 ->
                                        kSucceed (OrLeft deriv1 deriv2) more2,
                                    more1),
                                      -- kFail:
                                      leave_alone)
        focus -> leave_alone ()


{-
  prove_all: Given a context and a formula,
             collect all possible derivations that prove the formula (according to the rules given in a3.pdf).
-}
prove_all :: Context -> Formula -> [Derivation]
prove_all ctx goal = prove_core ctx goal (\deriv -> \more -> deriv : (more ()),
                                      \() -> [])

{-
  prove: Given a context and a formula,
         return True if the formula is provable using the rules given in a3.pdf,
            and False otherwise.
-}
prove :: Context -> Formula -> Bool
prove ctx goal = prove_core ctx goal (\deriv -> \more -> True,
                                      \() -> False)

test_imp1 = prove [Implies vB vC] (Implies vB vC)
test_imp2 = prove [Implies vB vC] (Implies (And vB vB) vC)
test_imp3 = not (prove [Implies (And vB vD) vC] (Implies vB vC))

test_imps = test_imp1 && test_imp2 && test_imp3

test_or1 = prove [Or vA vB] (Or vB vA)
test_or2 = prove [Or vC (And vA (Implies vA vB))] (Or vB vC)
test_or3 = prove [vA, Or (Implies vA vB) (Implies vA vC)] (Or vB (Or vB vC))
test_or4 = not (prove [Or vC (And vA (Implies vA vD))] (Or vB vC))
test_or5 = elem (OrRight 1 (UseAssumption vB)) (prove_all [vA, vB] (Or vB vA))
        && elem (OrRight 2 (UseAssumption vA)) (prove_all [vA, vB] (Or vB vA))
test_ors = test_or1 && test_or2 && test_or3 && test_or4 && test_or5



{-
  Q4 bonus: See a3.pdf.  If you do the bonus, COPY THIS FILE into a3bonus.hs first.
            Submit both files.
-}
