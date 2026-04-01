# Formal BQN
End goal is a formalized BQN grammer and small-step semantic in Agda.  
So far I've specified a abstract-syntax heavily copy-pasted from the [actual grammer](https://mlochbaum.github.io/BQN/spec/grammar.html).

The abstract syntax in Agda is a bunch of types representing the nodes of the syntax tree, and the rules to construct them are constructors for those types.

An example of a simple Small-step Semantic is [Bims](https://github.com/Brian-ED/transition-and-trees/blob/0050347608217ca0cc9200891bfff7b67d25bcf1/Bims.agda#L551-L576).

To be clear, I'm personally focussing fully on the Small-Step Semantic for now because I find it fun, but this project's goal is formalizing all reasonably-specifiable aspects of BQN, including parsing.
