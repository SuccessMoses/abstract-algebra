import Game.Levels.MonoidWorld.L01_Monoid
import Game.Levels.MonoidWorld.L02_instanceMonoid
import Game.Levels.MonoidWorld.L03_ListProd
import Game.Levels.MonoidWorld.L04_finRange
import Game.Levels.MonoidWorld.L05_mapFinRangePerm
import Game.Levels.MonoidWorld.L06_finRangeMapCompPerm
import Game.Levels.MonoidWorld.L07_prodSingleton
import Game.Levels.MonoidWorld.L08_prodConcat
import Game.Levels.MonoidWorld.L09_prodNeq
import Game.Levels.MonoidWorld.L10_prodEqOne
import Game.Levels.MonoidWorld.L11_finRangeSucc
import Game.Levels.MonoidWorld.L12_prodFinRangeSuccLast

World "MonoidWorld"
Title "Monoid World"

Introduction "
Welcome to Moniod World! In this world you learn how to define a monoid mathlib style.
You will also learn about some basic theorem proving in lean.

Mathlib defined the type constructor `Monoid` for a multiplicative monoid. This is
because the Monoid class extends `Mul` and `One`, hence (1 : Monoid M) for type M and
the binary operator '*' works for (x y : M). There is also `AddMonoid` which is
mathlib's notation for additive monoid, and this class extends `Add`, `Zero` and `Neg`.
Hence the binary operator '+' and the literal '0' is defined for `AddMonoid`

You will prive theorems in this game by using tools called *tactics*. The aim is to
prove thoerems by applying tactics in the right order.
"
