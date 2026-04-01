# kumar-b-tla

This repository contains artefacts accompanying a paper on the formal development
of Kumar's algorithm for termination detection using the Event-B and TLA+ methods.

## event-b directory

These files contain the Rodin and ProB projects underlying the development of
Kumar's termination detection algorithm in Event-B.

- TDAbstract: high-level problem specification of termination detection
- KumarAbstract: very similar to TDAbstract but using sent/received message counters
- KumarDaemon: introducing the daemon state and action, but still abstract detection
- KumarConcrete: localized termination detection, full invariant based on two ghost variables

## tla directory

These files contain similar developments in TLA+.

- AsyncTerminationDetection: high-level problem specification
- KumarTerminationDetection: model of Kumar's algorithm in TLA+

The .cfg files contain small instances for model checking using TLC.
Note: model checking KumarTerminationDetection runs into state-space explosion,
even for tiny model sizes.

The modules _proof.tla contain correctness (and refinement) proofs that can be
checked using TLAPS.
