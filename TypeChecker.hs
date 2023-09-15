
module TypeChecker where
import Grammar
import Lexer

-- Type alias for type environments.

type TypeEnv = [(String,TypeExp)]

-- Function for retrieving types of variables form the environment.

lookup::String -> [(String,a)] -> a
lookup s  []                    = error ("Type " ++ s ++ " not defined in the current environment")
lookup s1 ((s2,t):l) | s1 == s2 = t
lookup s  (_:l)                 = TypeChecker.lookup s l

-- Please complete the definition of typeChecker for the rest of the abstract syntax.

typeChecker:: AST -> TypeEnv -> TypeExp
typeChecker (Boolean _) _ = BoolType
typeChecker (Integer _) _ = IntType
typeChecker (Variable s) env = TypeChecker.lookup s env
typeChecker (Plus a b) env | typeChecker a env == IntType && typeChecker b env == IntType = IntType
typeChecker (Minus a b) env | typeChecker a env == IntType && typeChecker b env == IntType = IntType
typeChecker (Times a b) env | typeChecker a env == IntType && typeChecker b env == IntType = IntType
typeChecker (Quot a b) env | typeChecker a env == IntType && typeChecker b env  == IntType = IntType
typeChecker (Rem a b) env | typeChecker a env == IntType && typeChecker b env == IntType = IntType
typeChecker (And a b) env | typeChecker a env == BoolType && typeChecker b env == BoolType = BoolType
typeChecker (Or a b) env | typeChecker a env == BoolType && typeChecker b env == BoolType = BoolType
-- Operators
-- Comment: Equals, Gt, and Lt should only work on pair of IntType or pairs of
--          BoolType.  Yours also works on Arrow types.
typeChecker (Equals a b) env | typeChecker a env == typeChecker b env = BoolType
typeChecker (Gt a b) env | typeChecker a env == typeChecker b env = BoolType 
typeChecker (Lt a b) env | typeChecker a env == typeChecker b env = BoolType
-- Let
-- Comment: It is correct to include the type binding (x,s) in your type environment for b,
--          However, you are forgetting all of the other type bindings.
--          Your TypeChecker fails on this code
--           let x = 3 in let y = 5 in x + y
--          because it forgets that x is an integer when it tries to check x + y.
typeChecker (Let x a b) env = let s = typeChecker a env in typeChecker b [(x, s)]
typeChecker (If a b c) env | typeChecker a env == BoolType && 
    typeChecker b env == typeChecker c env = typeChecker b env
-- Lambda:
-- Comment:  Your mistake here is similar than that for Let.
typeChecker (Lambda a b c d) env | typeChecker b [(a, c)] == d = Arrow c d
-- App
-- Comment:  This is a case against overuse of guards.  You call "typeChecker a env" twice.
typeChecker (App a b) env | let Arrow s t = typeChecker a env in typeChecker b env == s = 
    let Arrow s t = typeChecker a env in t