# Democracy
Election-based consensus algorithm for a distributed system in the Isabelle theorem prover.

Warning: my proofs are very ugly! This was my first big Isabelle project, so I was more focused on getting things to run at all than on keepng things organized and readable.

Uses a slightly modified version of Martin Kleppman's Isabelle model of a distributed system available at https://gist.github.com/ept/b6872fc541a68a321a26198b53b3896b
(The important difference between Martin's Network.thy and my MyNetwork.thy is the addition of the set of procs as input for the step function. In the context of Democracy.thy, this modification allows the acceptor's step function to determine a winning value only once all proposers in the specified set of procs have voted.)
