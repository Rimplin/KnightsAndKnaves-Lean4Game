import Game.Metadata
import Game.Levels.KnightsAndKnaves2.L01_Introduction
import Game.Levels.KnightsAndKnaves2.L02_iff
import Game.Levels.KnightsAndKnaves2.L03_
import Game.Levels.KnightsAndKnaves2.L04_orIff
import Game.Levels.KnightsAndKnaves2.L05_imp
World "KnightsAndKnaves2"
Title "Knights and Knaves, second approach"
Introduction
"
In this world, we deal with the knights and knaves puzzle but the difference is how we translate and represent the problem in Lean.(an arguably cleaner representation/translation)

The setup is as follows:
We exploit the binary nature of an inhabitant. An inhabitant can be either/or. There are two options and no third, either a knight or a knave. So, we declare as variables a proposition for every inhabitant. Say we have three inhabitants A,B,C , we declare the following propositions:
```
variable {A B C : Prop}
```
Now we intrepret having a proof of `A` as `A` being a knight, and having a proof of `¬A` as `A` being a knave.

The translation of statements made by each inhabitant into a propositional formula remains the same, using `↔` but of course instead of `A ∈ Knight` we just have `A` and instead of `A ∈ Knave` we just have `¬A`.

-- correspondence
Notice that there are no explicit assumptions in this representation, but that doesn't mean that this representation is less faithful. We know that any proposition is either true or false, in our context this would translate to every inhabitant is either a knight or a knave. Moreoever, we know that p ∧ ¬p is false, which would translate to the fact that no inhabitant can be both a knight or a knave(which within the previous representation of finite sets, would mean that the set knight and the set knave are disjoint). 
we can also do 1's and zero's stuff, more related to smt solvers. if your interestedyou can check this really short video that would present the idea.
include these videos:
knights and knaves prolog - Invidious
https://yewtu.be/search?q=knights+and+knaves+prolog


Knights and Knaves in Prolog - YouTube
https://www.youtube.com/watch?v=oEAa2pQKqQU


All puzzles were generated(and possibly modified) from https://www.wolframcloud.com/objects/demonstrations/KnightsAndKnavesPuzzleGenerator-source.nb.
"
