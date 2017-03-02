package sigmastate.utxo

import scorex.core.serialization.Serializer
import sigmastate.Proof.Challenge
import sigmastate.SigmaProposition.PropositionCode
import sigmastate._


case class TestingReducerInput(override val height: Int) extends BlockchainState


object TestingInterpreter extends Interpreter {
  override type SProp = StateProposition
  override type Context = TestingReducerInput


  override type CProp = DLogProposition
  override type CProof = FakeSchnorrSignature.type

  override val maxDepth = 50

  override def statefulReductions[SP <: StateProposition](proposition: SP, environment: TestingReducerInput): BooleanConstantProposition =
    proposition match {
      case HeightFromProposition(from) =>
        if (environment.height >= from) TrueProposition else FalseProposition
      case HeightBetweenProposition(from, until) =>
        if (environment.height >= from && environment.height < until) TrueProposition else FalseProposition
      case HeightUntilProposition(until) =>
        if (environment.height < until) TrueProposition else FalseProposition
    }
}


object FakeSchnorrSignature extends Proof[DLogProposition] {
  override val propCode: PropositionCode = DLogProposition.Code

  override def verify(proposition: DLogProposition, challenge: Challenge): Boolean =
    proposition.bytes.sameElements(challenge)

  override type M = this.type

  override def serializer: Serializer[FakeSchnorrSignature.type] = ???
}