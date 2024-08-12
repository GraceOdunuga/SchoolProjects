-- CISC 360 a1, Fall 2023

module A1 where

-- Rename this file to include your student ID: a1-studentid.hs
-- Also, add your student ID number after the "=":
student_id :: Integer
student_id = 20292380

-- THIS FILE WILL NOT COMPILE UNTIL YOU ADD YOUR STUDENT ID ABOVE
check_that_you_added_your_student_ID_above = ()


{-
Q1:
   square (m, n)  ==  True
   if and only if
                           2
     n is m squared  (n = m )

     or
                           2
     m is n squared  (m = n )
-}
square :: (Integer, Integer) -> Bool
square (m, n) = (n == m^2) || (m == n^2)

{-
  Testing square:

  CISC 360 CONVENTION:
  Every variable beginning with "test_" should evaluate to True.
  So test_square1 should be True because  square 1 (-1)  should equal True,
  test_square2 should be True because  (square 5 2)  should equal False,
  and so on.
-}
test_square1, test_square2, test_square3, test_square4, test_square5, test_square6 :: Bool
test_square1 = (square (1, -1)) == True
test_square2 = (square (5, 2)) == False
test_square3 = (square (-2, 0)) == False
test_square4 = (square (2, 5)) == False
test_square5 = (square (65536, 256)) == True
test_square6 = (square (65536, 255)) == False

-- Do all square tests together
test_square :: Bool
test_square = test_square1 && test_square2
                           && test_square3
                           && test_square4
                           && test_square5
                           && test_square6

{-
Q2:
  `spiral': given two integers `dir' and `span',
  returns 1 if `dir' is less than or equal to 0,
  and otherwise returns (span - dir) * spiral (span - dir) (span - 4).
-}

spiral :: Integer -> Integer -> Integer
spiral dir span = if dir <= 0 then 1 else (span - dir) * spiral (span - dir) (span - 4)


-- Testing spiral:
test_spiral1, test_spiral2, test_spiral3, test_spiral4, test_spiral :: Bool
test_spiral1 = ((spiral 0 32)    == 1)
test_spiral2 = ((spiral (-32) 5) == 1)
test_spiral4 = ((spiral 13 3)    == -10)
test_spiral3 = ((spiral 7 6000)  == -107676231)

test_spiral  = test_spiral1 && test_spiral2 && test_spiral3 && test_spiral4


{-
Q3: 
  spiral_seq n == string containing results of  spiral k 260  for k in 1, ..., n
                   separated by semicolons

  For example,  spiral_seq 3  should return  "-777;-516;-257"
    because spiral 1 260 should return -777,
            spiral 2 260 should return -516,
        and spiral 3 260 should return -257.

  If n < 1, spiral_seq should return the empty string: ""
  
  Hints:
     1. The built-in function  show  converts an integer
        to its (decimal) representation as a string.

     2. You can use the built-in function  ++  to concatenate strings.
          For example, "10" ++ "," == "10,".

     3. You may find it useful to define a helper function for spiral_seq to call.
-}
spiral_seq :: Integer -> String
spiral_seq n = if n == 0 
	       then ""
	       else spiral_seg2 1 n ""
       

-- The helper function `spiral_seg2` recursively generates segments of a spiral sequence.
spiral_seg2 :: Integer -> Integer -> String -> String
spiral_seg2 curr n str 
			| curr < n		= spiral_seg2 (curr+1) n (str ++ show (spiral curr 260) ++ ";")
			| curr == n		= spiral_seg2 (curr+1) n (str ++ show (spiral curr 260))
			| otherwise 		= str

{-
Q4: Stepping

   Give your answers by filling in the blanks below,
   **including the substitution** in function application steps, as described.

Q4.1: Replace the underlines (_______).

     expression                   justification

     (\q -> 1 + (q * 2)) 6

  => 1 + (6 * 2)		  By function application with 6 for q	    		
  => 1 + (12)			  By arithmetic of 6 * 2
  => 13                      	  by arithmetic 1 + 12

  For full marks, state the substitution in the function application step.
  For example:

  "...                          by function application
                                with 500 for q"
                                     ^^^^^^^^^
                          "500 for q" is the substitution

Q4.2: Replace the underlines (_______).
      Assume a function `incr' has been defined:
-}
incr :: Integer -> Integer
incr x = x + 1
{-
     expression                            justification

     (if True then incr else (\z -> 0)) 9

  => incr 9				   by if-then-else
  => x + 1				   by function application with 9 for x
   = 9 + 1
  => 10 				   by arithmetic

  For full marks, state the substitution in all function application steps.

Q4.3: 
  Step the following expression.  (It can only be stepped once.)
  (You cannot directly check the answer in Haskell,
   because Haskell will not print functions.)

     expression                            justification

     (\x -> (\y -> (0, x))) incr

  => (\y -> (0, incr))			   By function application with incr for x
-}
