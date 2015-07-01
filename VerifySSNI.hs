-- | Using SMT model checking to verify instruction single step noninterference (SSNI).
module Main (main) where

import Control.Monad.State hiding (guard)
import Data.SBV
import Prelude hiding (init)
import Text.Printf

infix  9 :@
infix  4 :==, :<=, :<
infixr 0 <==, =:

{-
Machine Description:

The machine state is comprised of a PC and a memory, with the top elements of the
memory being the general purpose register set.  Each state element, including the PC,
carries a value (Word8) and a label (Bool).  Currently the memory is only 4 atoms deep.

The Mem expression is used to access a memory location or a register:

  Mem 3  -- References atom at address 3.

Most instructions take registers as arguments.  These arguments are accessable via the
expressions Arg1, Arg2, and Arg3.  Because the register file is part of the memory,
register arguments are turned into memory references.  For example, the semantics of:

  ADD reg1 reg2 reg3

could be written as:

  PC <== PC + 1
  Mem Arg3 <== Mem Arg1 + Mem Arg2

Likewise, operands that hold pointers would need two Mem expressions to
dereference the pointer:

  CPMR addr dst

could look like:

  PC <== PC + 1
  Mem Arg2 <== Mem (Mem Arg1)

-}

main :: IO ()
main = do

  -- ADD op1 op2 result

  verifySSNI "ADD*1" $ do
    PC <== PC + 1
    Mem Arg3 <== Mem Arg1 + Mem Arg2

  verifySSNI "ADD*2" $ do
    PC <== (PC + 1) :@ Label PC
    Mem Arg3 <== Mem Arg1 + Mem Arg2

  verifySSNI "ADD*3" $ do
    PC <== (PC + 1) :@ Label PC
    Mem Arg3 <== (Mem Arg1 + Mem Arg2) :@ (Label (Mem Arg1) .|. Label (Mem Arg2))

  -- Conventional merging labels of operand and guard for no-sensitive-upgrades.
  verifySSNI "ADD*4" $ do
    PC <== (PC + 1) :@ Label PC
    let newLabel = Label (Mem Arg1) .|. Label (Mem Arg2) .|. Label PC
    Mem Arg3 <== (Mem Arg1 + Mem Arg2) :@ newLabel
    guard $ newLabel :<= Label (Mem Arg3)

  -- Assumes all labels are correct before operation.  Does not merge labels of operands.
  verifySSNI "ADD*5" $ do
    PC <== (PC + 1) :@ Label PC
    Mem Arg3 <== (Mem Arg1 + Mem Arg2) :@ Label (Mem Arg3)
    guard $ Label PC         :<= Label (Mem Arg3)
    guard $ Label (Mem Arg1) :<= Label (Mem Arg3)
    guard $ Label (Mem Arg2) :<= Label (Mem Arg3)

  -- Attempts to do the same thing as ADD*5, but with Navs instead of guards.
  -- But this fails.
  -- Q: Is it even possible for ADD to not have "stop-the-world" guard conditions?
  --    I though NaVs were our solution to these type of problems, but it doesn't appear so.
  verifySSNI "ADD*6" $ do
    let guard = (Label PC         :<= Label (Mem Arg3))
            .|. (Label (Mem Arg1) :<= Label (Mem Arg3))
            .|. (Label (Mem Arg2) :<= Label (Mem Arg3))
    PC <== (PC + 1) :@ Label PC
    Mem Arg3 <== (Mux guard (Mem Arg1 + Mem Arg2) Nav) :@ Label (Mem Arg3)


  -- LOAD srcAddrReg dstValueReg

  verifySSNI "LOAD*1" $ do
    PC <== (PC + 1) :@ Label PC
    Mem Arg2 <== Mem (Mem Arg1)

  verifySSNI "LOAD*2" $ do
    PC <== (PC + 1) :@ Label PC
    Mem Arg2 <== Mem (Mem Arg1) :@ Label (Mem Arg1)  -- Label with label from pointer.

  verifySSNI "LOAD*3" $ do
    PC <== (PC + 1) :@ Label PC
    let newLabel = Label (Mem Arg1) .|. Label (Mem (Mem Arg1)) .|. Label PC
    Mem Arg2 <== Mem (Mem Arg1) :@ newLabel
    guard $ newLabel :<= Label(Mem Arg2)


  -- STORE dstAddrReg srcValueReg

  verifySSNI "STORE*1" $ do
    PC <== (PC + 1) :@ Label PC
    Mem (Mem Arg1) <== Mem Arg2

  verifySSNI "STORE*2" $ do
    PC <== (PC + 1) :@ Label PC
    Mem (Mem Arg1) <== Mem Arg2 :@ Label (Mem Arg1)  -- Label with label from pointer.

  verifySSNI "STORE*3" $ do
    PC <== (PC + 1) :@ Label PC
    Mem (Mem Arg1) <== Mem Arg2 :@ (Label (Mem Arg1) .|. Label (Mem Arg2))  -- Label with label from pointer and data to be stored.

  verifySSNI "STORE*4" $ do
    PC <== (PC + 1) :@ Label PC
    let newLabel = Label (Mem Arg1) .|. Label (Mem Arg2) .|. Label PC
    Mem (Mem Arg1) <== Mem Arg2 :@ newLabel
    guard $ newLabel :<= Label (Mem (Mem Arg1))                     -- No-sensitive-upgrades rule.


  -- JMP offset   # Unconditional jump.

  verifySSNI "JMP" $ do
    PC <== (PC + Arg1) :@ Label PC


  -- BZ test offset     # Branch when test value is 0.

  verifySSNI "BZ*1" $ do
    PC <== (Mux (Mem Arg1) (PC + 1) (PC + Arg2)) :@ (Label PC)
    -- Q: Why doesn't BZ*1 require the PC to be raised by the label of the test value?

  verifySSNI "BZ*2" $ do
    PC <== (Mux (Mem Arg1) (PC + 1) (PC + Arg2)) :@ (Label PC .|. Label (Mem Arg1))  -- PC label is joined with conditional.


  -- LOADPC reg

  verifySSNI "LOADPC" $ do
    PC <== Mem Arg1

    -- Q: Why is this passing?  This should be invalid.
    

  -- CLASSIFY reg   # Raising the label on a value.
  verifySSNI "CLASSIFY" $ do
    PC <== (PC + 1) :@ Label PC
    Mem Arg1 <== Mem Arg1 :@ 1
    guard $ (Label PC :< 1) .|. Label (Mem Arg1)

  -- CLASSIFYPC   # Raises the PC.
  verifySSNI "CLASSIFYPC" $ do
    PC <== (PC + 1) :@ 1
 
  -- DECLASSIFYPC   # Lowers the PC.
  verifySSNI "DECLASSIFYPC" $ do
    PC <== (PC + 1) :@ 0            -- Q: This should be totally illegal, but it's not.

  -- LABELOF src dst
  verifySSNI "LABELOF" $ do
    PC <== (PC + 1) :@ 0
    Mem Arg2 <== Label (Mem Arg1) :@ 0

  verify $ do
    "ADD" =: do
      PC <== (PC + 1) :@ Label PC
      let newLabel = Label (Mem Arg1) .|. Label (Mem Arg2) .|. Label PC
      Mem Arg3 <== (Mem Arg1 + Mem Arg2) :@ newLabel
      guard $ newLabel :<= Label (Mem Arg3)

    "LOAD" =: do
      PC <== (PC + 1) :@ Label PC
      let newLabel = Label (Mem Arg1) .|. Label (Mem (Mem Arg1)) .|. Label PC
      Mem Arg2 <== Mem (Mem Arg1) :@ newLabel
      guard $ newLabel :<= Label(Mem Arg2)

    "STORE" =: do
      PC <== (PC + 1) :@ Label PC
      let newLabel = Label (Mem Arg1) .|. Label (Mem Arg2) .|. Label PC
      Mem (Mem Arg1) <== Mem Arg2 :@ newLabel
      guard $ newLabel :<= Label (Mem (Mem Arg1))                     -- No-sensitive-upgrades rule.

    "JMP" =: do
      PC <== (PC + Arg1) :@ Label PC

    "BZ" =: do
      PC <== (Mux (Mem Arg1) (PC + 1) (PC + Arg2)) :@ (Label PC)

    "LOADPC" =: do
      PC <== Mem Arg1

    "CLASSIFY" =: do
      PC <== (PC + 1) :@ Label PC
      Mem Arg1 <== Mem Arg1 :@ 1
      guard $ (Label PC :< 1) .|. Label (Mem Arg1)

    "CLASSIFYPC" =: do
      PC <== (PC + 1) :@ 1
 
    "DECLASSIFYPC" =: do
      PC <== (PC + 1) :@ 0

    "LABELOF" =: do
      PC <== (PC + 1) :@ 0
      Mem Arg2 <== Label (Mem Arg1) :@ 0


-- | Expressions for the instruction semantics language.
data E
  = PC                  -- ^ The PC.
  | Arg1 | Arg2 | Arg3  -- ^ Optional instruction arguments, e.g. LOAD R1 R0.  Label = public.
  | Label E             -- ^ Label of expression.  Label = public.
  | E :@ E              -- ^ Relabels a value.  Value = value of a, Label = value of b.
  | Mem E               -- ^ Memory access.  Value and label from memory at an address.
  | Const Word8         -- ^ A constant value.  Label = public.
  | Nav                 -- ^ A NaV value.  Label = public.
  | IsNav E             -- ^ Value is 0 if not Nav, 1 if Nav.  Label = public.
  | E :+ E              -- ^ Value = value of a + value of b.  Label = public.
  | And E E             -- ^ Bitwise AND of values.  Label = public.
  | Or  E E             -- ^ Bitwise OR  of values.  Label = public.
  | Not E               -- ^ Bitwise complement.  Label = public.
  | E :== E             -- ^ Values equal.  Label = public.
  | E :<= E             -- ^ Values less than or equal.  Label = public.
  | E :<  E             -- ^ Values less than.           Label = public.
  | Mux E E E           -- ^ Conditional (if else then).  Value and label from b or c.
  deriving (Show, Eq)

-- NOTE: At some point the semantics of E should be relaxed.  For example, the label of Arg1 should be nondeterinistic, not public.

instance Num E where
  (+) = (:+)
  (*) = undefined
  (-) = undefined
  abs = undefined
  signum = undefined
  fromInteger = Const . fromIntegral

instance Bits E where
  (.&.) = And
  (.|.) = Or
  complement = Not
  xor = undefined
  bitSize = undefined
  isSigned = undefined

type InstructionSet = State [(String, [Trans])]

type Instruction = State [Trans]

-- | Defines an instruction.
(=:) :: String -> Instruction () -> InstructionSet ()
name =: semantics = modify $ \ m -> m ++ [(name, execState semantics [])]

data Trans = Assign E E | Guard E

-- | State transition operator.
(<==) :: E -> E -> Instruction ()
a <== b = modify $ \ m -> m ++ [Assign a b]

-- | A guard condition on an instruction.  Machine terminates if not true.
guard :: E -> Instruction ()
guard a = modify $ \ m -> m ++ [Guard a]

-- | Verifies a transition is SSNI or displays a counter example.
verifySSNI :: String -> Instruction () -> IO ()
verifySSNI name t = do
  SatResult result <- satWith cvc4 $ do
    arg1 <- sWord8 "Arg1"
    arg2 <- sWord8 "Arg2"
    arg3 <- sWord8 "Arg3"
    m <- machines
    let args = (arg1, arg2, arg3)
        (guards, pc', memUpdates) = updates t
        guard = bAnd [ (value $ eval args (init1 m) g) ./= 0 &&& (value $ eval args (init2 m) g) ./= 0 | g <- guards ]
    return $ bAnd
      [ guard                            -- All guard conditions are true.
      , noTransMem args m memUpdates     -- Transition relation for memories not updated.
      , transMem   args m memUpdates     -- Transition relation for memories updated.
      , transPC    args m pc'            -- Transition relation for PC.
      , bnot $ ssni indistinguishable m  -- SSNI property.  (Negated because a sat means a failure to meet property.)
      ]

  case result of
    Unsatisfiable _ -> putStrLn $ "PASS " ++ name
    Satisfiable config model -> do
      putStrLn $ "FAIL " ++ name
      putStrLn ""
      putStrLn $ counterExample name $ show $ SatResult $ Satisfiable config model
      putStrLn ""
    _ -> putStrLn $ "ERROR " ++ name ++ ": " ++ show (SatResult result)

-- | Verify than an instruction set is SSNI.
verify :: Lattice -> InstructionSet () -> IO ()
verify _ _ = return ()

-- | A lattice an acyclic graph of principals.
type Lattice = [(String, String)]

simple :: Lattice
simple = [("public", "secret")]

multiLevel :: Lattice
multiLevel =
  [ ("unclassified", "classified")
  , ("classified", "secret")
  , ("secret", "top-secret")
  ]

diamond :: Lattice
diamond = 
  [ ("bottom", "left")
  , ("bottom", "right")
  , ("left",   "top")
  , ("right",  "top")
  ]

-- | An Atom is a NaV flag, a value, and a label.
data Atom = Atom 
  { isnav :: SBool
  , value :: SWord8
  , label :: SBool
  } deriving Show

-- | The machine state is the PC and the memory.
data Machine = Machine
  { pc
  , m0
  , m1
  , m2
  , m3 :: Atom
  } deriving Show

-- | The 4 machines states.
data Machines = Machines
  { init1
  , init2
  , next1
  , next2 :: Machine
  } deriving Show

-- | Indistinguishability between machines with NaVs.
indistinguishable :: Machine -> Machine -> SBool
indistinguishable a b = bAnd
  [ (label $ pc a) .== (label $ pc b)
  , (bnot $ label $ pc a) ==> valuesEqual (pc a) (pc b)
  , bAnd [ (label $ m a) &&& (label $ m b) ||| (bnot $ label $ m a) &&& (bnot $ label $ m b) &&& valuesEqual (m a) (m b) | m <- [m0, m1, m2, m3] ]
  ]
  where
  valuesEqual :: Atom -> Atom -> SBool
  valuesEqual a b = isnav a &&& isnav b ||| (bnot $ isnav a) &&& (bnot $ isnav b) &&& value a .== value b

-- | Single step noninterference, parameterized by indistinguishability.
ssni :: (Machine -> Machine -> SBool) -> Machines -> SBool
ssni indistinguishable m = bAnd
  [ (bnot $ label $ pc $ init1 m) &&& (bnot $ label $ pc $ init2 m) &&& indistinguishable (init1 m) (init2 m) ==> indistinguishable (next1 m) (next2 m)  -- Condition 1 of SSNI.
  , (label $ pc $ init1 m) &&& (label $ pc $ next1 m) ==> indistinguishable (init1 m) (next1 m) -- Condition 2 of SSNI.
  , (label $ pc $ init2 m) &&& (label $ pc $ next2 m) ==> indistinguishable (init2 m) (next2 m) -- Condition 2 of SSNI.
  , (label $ pc $ init1 m) &&& (label $ pc $ init2 m) &&& indistinguishable (init1 m) (init2 m) &&& (bnot $ label $ pc $ next1 m) &&& (bnot $ label $ pc $ next2 m) ==> indistinguishable (next1 m) (next2 m)  -- Condition 3 of SSNI.
  ] -- XXX Not sure how to handle condition 4 or SSNI.

-- | Creates the four machines: init1, init2, next1, next2.
machines :: Symbolic Machines
machines = do
  init1 <- machine "Init" 1
  init2 <- machine "Init" 2
  next1 <- machine "Next" 1
  next2 <- machine "Next" 2
  return $ Machines init1 init2 next1 next2
  where
  machine :: String -> Int -> Symbolic Machine
  machine phase trace = do
    pc <- atom "PC"
    m0 <- atom "M0"
    m1 <- atom "M1"
    m2 <- atom "M2"
    m3 <- atom "M3"
    return $ Machine pc m0 m1 m2 m3
    where
    atom :: String -> Symbolic Atom
    atom name = do
      isnav <- sBool  $ name ++ phase ++ "IsNav" ++ show trace
      value <- sWord8 $ name ++ phase ++ "Value" ++ show trace
      label <- sBool  $ name ++ phase ++ "Label" ++ show trace
      return $ Atom isnav value label
  
-- | The memory of the Machine.
memory :: Machine -> [Atom]
memory m = [m0 m, m1 m, m2 m, m3 m]

-- | Transition relation for PC.
transPC :: Args -> Machines -> E -> SBool
transPC args m pc' = bAnd
  [ (isnav $ pc $ next1 m) .== isnav pc1'
  , (value $ pc $ next1 m) .== value pc1'
  , (label $ pc $ next1 m) .== label pc1'
  , (isnav $ pc $ next2 m) .== isnav pc2'
  , (value $ pc $ next2 m) .== value pc2'
  , (label $ pc $ next2 m) .== label pc2'
  ]
  where
  pc1' = eval args (init1 m) pc'
  pc2' = eval args (init2 m) pc'

-- | Transition memory elements that are not updated, i.e. not addressed.
noTransMem :: Args -> Machines -> [(E, E)] -> SBool
noTransMem args machines updates = bAnd
  [ (bnot (bOr [ (bnot $ isnav $ eval args (init1 machines) addr) &&& i .== (value $ eval args (init1 machines) addr) | (addr, _) <- updates ]) ==> noChange init1 next1 m) &&&
    (bnot (bOr [ (bnot $ isnav $ eval args (init2 machines) addr) &&& i .== (value $ eval args (init2 machines) addr) | (addr, _) <- updates ]) ==> noChange init2 next2 m)
  | (i, m) <- zip [0 ..] [m0, m1, m2, m3]
  ]
  where
  noChange :: (Machines -> Machine)  -> (Machines -> Machine) -> (Machine -> Atom) -> SBool
  noChange m1 m2 a = bAnd
    [ (isnav $ a $ m1 machines) .== (isnav $ a $ m2 machines)
    , (value $ a $ m1 machines) .== (value $ a $ m2 machines)
    , (label $ a $ m1 machines) .== (label $ a $ m2 machines)
    ]

-- | Applies a transition relation for an updated memory element.
transMem :: Args -> Machines -> [(E, E)] -> SBool
transMem args machines updates = bAnd
  [ (bnot $ isnav $ eval args init addr) &&& i .== (value $ eval args init addr) ==> bAnd
    [ (isnav $ m next) .== (isnav $ eval args init nextValue)
    , (value $ m next) .== (value $ eval args init nextValue)
    , (label $ m next) .== (label $ eval args init nextValue)
    ]
  | (i, m) <- zip [0 ..] [m0, m1, m2, m3], (addr, nextValue) <- updates, (init, next) <- [(init1 machines, next1 machines), (init2 machines, next2 machines)]
  ]

type Args = (SWord8, SWord8, SWord8)

-- | Evaluates an expression of the machine state.
eval :: Args -> Machine -> E -> Atom
eval args@(arg1, arg2, arg3) m a = case a of
  PC   -> pc m
  Arg1 -> Atom false arg1 false
  Arg2 -> Atom false arg2 false
  Arg3 -> Atom false arg3 false
  Label a -> Atom false (ite l 1 0) false
    where
    Atom _ _ l = eval args m a
  IsNav a -> Atom false (ite n 1 0) false
    where
    Atom n _ _ = eval args m a
  a :@ b -> Atom aN aV $ bV ./= 0
    where
    Atom aN aV _ = eval args m a
    Atom _  bV _ = eval args m b  -- XXX What happens if this is NaV?
  Const a -> Atom false (fromIntegral a) false
  Nav     -> Atom true 0 false
  a :+ b  -> Atom (aN ||| bN) (aV + bV) false
    where
    Atom aN aV _ = eval args m a
    Atom bN bV _ = eval args m b
  And a b -> Atom (aN ||| bN) (aV .&. bV) false
    where
    Atom aN aV _ = eval args m a
    Atom bN bV _ = eval args m b
  Or a b -> Atom (aN ||| bN) (aV .|. bV) false
    where
    Atom aN aV _ = eval args m a
    Atom bN bV _ = eval args m b
  Not a -> Atom aN (complement aV) false
    where
    Atom aN aV _ = eval args m a
  a :== b -> Atom (aN ||| bN) (ite (aV .== bV) 1 0) false
    where
    Atom aN aV _ = eval args m a
    Atom bN bV _ = eval args m b
  a :<= b -> Atom (aN ||| bN) (ite (aV .<= bV) 1 0) false
    where
    Atom aN aV _ = eval args m a
    Atom bN bV _ = eval args m b
  a :<  b -> Atom (aN ||| bN) (ite (aV .<  bV) 1 0) false
    where
    Atom aN aV _ = eval args m a
    Atom bN bV _ = eval args m b
  Mux a b c -> Atom (aN ||| ite (aV ./= 0) bN cN) (ite (aV ./= 0) bV cV) (ite (aV ./= 0) bL cL)
    where
    Atom aN aV _  = eval args m a
    Atom bN bV bL = eval args m b
    Atom cN cV cL = eval args m c
  Mem a -> Atom
    (n ||| (select (map isnav $ memory m) false $ addr `sMod` 4))
    (select (map value $ memory m) 0     $ addr `sMod` 4)
    (select (map label $ memory m) false $ addr `sMod` 4)
    where
    Atom n addr _ = eval args m a

-- | Extracts the guard conditions, the next PC expression, and the memory updates with addresses.
updates :: Instruction () -> ([E], E, [(E, E)])
updates trans'
  | null pc                                        = error $ "No PC update specified for instruction."
  | length pc > 1                                  = error $ "Instruction has multiple PC updates."
  | length trans /= length mem + 1 + length guards = error $ "Instruction has invalid transitions."
  | otherwise                                      = (guards, head pc, mem)
  where
  trans = execState trans' []
  pc = [ b | Assign PC b <- trans ]
  mem = [ (addr, b) | Assign (Mem addr) b <- trans ]
  guards = [ a | Guard a <- trans ]

-- | Formats a counter example from a model.
counterExample :: String -> String -> String
counterExample instr a = unlines $ map ("  " ++) $ [printf "%s %s %s %s" instr (var "Arg1") (var "Arg2") (var "Arg3"), ""] ++ map format states
  where
  states = ["PC", "M0", "M1", "M2", "M3"]

  vars :: [(String, String)]
  vars = [ (words l !! 0, words l !! 2) | l <- lines a, length (words l) >= 3 ]

  var :: String -> String
  var n = case lookup n vars of
    Nothing -> "_"
    Just a  -> a

  value :: String -> String -> Int -> String
  value name phase trace = case var $ name ++ phase ++ "IsNav" ++ show trace of
    "True"  -> "nav"
    "False" -> var $ name ++ phase ++ "Value" ++ show trace
    _ -> "_"
    
  label :: String -> String -> Int -> String
  label name phase trace = case var $ name ++ phase ++ "Label" ++ show trace of
    "True"  -> "secret"
    "False" -> "public"
    _       -> "_"

  format :: String -> String
  format name = printf "%2s = %3s@%s  %3s@%s  ->  %3s@%s  %3s@%s" name
    (value name "Init" 1) (label name "Init" 1)
    (value name "Init" 2) (label name "Init" 2)
    (value name "Next" 1) (label name "Next" 1)
    (value name "Next" 2) (label name "Next" 2)

