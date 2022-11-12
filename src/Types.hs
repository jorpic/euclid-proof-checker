module Types where

import Prelude hiding (Ordering(..))
import Data.Text qualified as S

data Fn
  = BR | FR | TF
  | BE |      EQ | NE | CO | NC
  | EE | TR | EA | ON | RA | IC
  | OC | CI | CU | SU | TC | LT
  | ME | CR | SS | OS | AO | EL
  | RR | MI | IS | PA | PR | TP
  | PE | TG | TT | IA | RT | AS
  | PG | SQ | EF | ET | RE | RC
  | ER | TE | FE
  deriving (Eq, Ord, Show, Read)

arity :: Fn -> Int
arity = \case
  -- vvv FIXME: These three were added by me.
  --            They are defined in Definitions.txt
  BR -> 5 -- base rectangle
  FR -> 8 -- figurerectangle
  TF -> 7 -- triangle ABC is equal to quadrilateral abcd
  --
  BE -> 3 -- ABC are in order, that is, B is between A and C
  -- vvv FIXME: This one clashes with "equal triangles".
  --            Judging by arity, it is not used in proofs.
  --  TE -> 3 -- non-strict betweenness
  EQ -> 2 -- A and B are equal
  NE -> 2 -- A and B are unequal
  CO -> 3 -- A, B, and C are collinear
  NC -> 3 -- not collinear
  EE -> 4 -- AB is congruent to CD
  TR -> 3 -- ABC is a triangle, same as noncollinear
  EA -> 6 -- angle ABC is equal to angle abc
  ON -> 2 -- A is on circle J
  RA -> 3 -- Ray BA contains point C
  IC -> 2 -- A is inside J
  OC -> 2 -- A is outside J
  CI -> 4 -- J is the circle of center C and radius AB
  CU -> 5 -- AB and CD cut each other in E
  SU -> 5 -- ABC and DBF are supplementary angles
  TC -> 6 -- ABC and abc are congruent triangles
  LT -> 4 -- AB < CD,  segment ordering
  ME -> 4 -- line AB meets line CD 
  CR -> 4 -- segment AB meets segment CD
  SS -> 4 -- SSCDAB means C and D are on the same side of AB
  OS -> 4 -- OSCABD  means C and d are on opposite sides of AB
  AO -> 6 -- angle ABC < angle DEF
  EL -> 3 -- ABC is equilateral
  RR -> 3 -- ABC is a right angle
  MI -> 3 -- MABC means B is a (the) midpoint of AC
  IS -> 3 -- ABC is isoceles, i.e. AB=AC and ABC is a triangle.
  PA -> 5 -- PQ perpendicular to AB at C
  PR -> 4 -- AB is parallel to CD
  TP -> 4 -- AB is Tarski-parallel to CD
  PE -> 4 -- PQ perpendicular to AB
  TG -> 6 -- AB + CD > EF
  TT -> 8 -- AB + CD > EF + GH, used only in I.21
  IA -> 4 -- IABCD means D is in the interior of angle ABC
  RT -> 6 -- ABC and DEF make together two right angles
  AS -> 9 -- ABC+DEF=PQR
  PG -> 4 -- ABCD is a parallelogram
  SQ -> 4 -- ABCD is a square
  EF -> 8 -- ABCD and abcd are equal quadrilaterals; in particular they have equal area
  ET -> 6 -- ABC and DEF are equal triangles
  RE -> 4 -- ABCD is a rectangle
  RC -> 8 -- ABCD and abcd are congruent rectangles
  ER -> 8 -- ABCD and abcd are equal rectangles (defined)
  TE -> 6 -- defined "equal triangles"
  FE -> 8 -- defined "equal quadrilaterals"

-- Expression mixes logical functors like NO, AN, OR, and geometrical
-- relations (all other functors).
data Expr
  = AN [Expr]
  | OR [Expr]
  | NO Expr
  | Fun Fn [Char]
  deriving (Show, Eq, Ord)


-- Proposition is either implication or equivalence.
data Prop = Prop
  { from :: [Expr]   -- antecedent = conjunction of expressions
                     --   (can be empty, e.g. `EQ A A`)
  , ex   :: [Char]   -- existential variables
  , to   :: Expr     -- consequent
  }
  deriving (Eq, Show)

type Proof = [ProofBlock]
data ProofBlock
  = Infer Expr S.Text
  | Reductio Expr Expr Proof
  | Cases Expr [(Expr, Proof)]
  deriving (Eq, Show)
