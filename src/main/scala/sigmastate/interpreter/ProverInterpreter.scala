package sigmastate.interpreter

import org.bitbucket.inkytonik.kiama.relation.Tree
import scapi.sigma.rework.DLogProtocol.DLogNode
import sigmastate._

import scala.util.Try

/**
  * Proof generated by a prover along with possible context extensions
  */
case class ProverResult[ProofT <: UncheckedTree](proof: ProofT, extension: ContextExtension)

trait ProverInterpreter extends Interpreter {

  val contextExtenders: Map[Int, ByteArrayLeaf]

  def enrichContext(tree: SigmaStateTree): ContextExtension = {
    val targetName = CustomByteArray.getClass.getSimpleName.replace("$", "")

    val ce = new Tree(tree).nodes.flatMap { n =>
      if (n.productPrefix == targetName) {
        val tag = n.productIterator.next().asInstanceOf[Int]
        contextExtenders.get(tag).map(v => tag -> v)
      } else None
    }.toMap

    ContextExtension(ce)
  }

  protected def prove(unprovenTree: UnprovenTree): ProofT

  def normalizeUnprovenTree(unprovenTree: UnprovenTree): UnprovenTree

  def prove(exp: SigmaStateTree, context: CTX, challenge: ProofOfKnowledge.Message): Try[ProverResult[ProofT]] = Try {
    val candidateProp = reduceToCrypto(exp, context).get

    val (cProp, ext) = (candidateProp.isInstanceOf[SigmaT] match {
      case true => (candidateProp, ContextExtension(Map()))
      case false =>
        val extension = enrichContext(candidateProp)
        //todo: no need for full reduction here probably
        (reduceToCrypto(candidateProp, context.withExtension(extension)).get, extension)
    }).ensuring{res =>
      res._1.isInstanceOf[BooleanConstantNode] ||
        res._1.isInstanceOf[CAND] ||
        res._1.isInstanceOf[COR2] ||
        res._1.isInstanceOf[DLogNode]}


    ProverResult(cProp match {
      case tree: BooleanConstantNode =>
        tree match {
          case TrueConstantNode => NoProof
          case FalseConstantNode => ???
        }
      case _ =>
        val ct = TreeConversion.convertToUnproven(cProp.asInstanceOf[SigmaT]).withChallenge(challenge)
        val toProve = normalizeUnprovenTree(ct)
        prove(toProve)
    }, ext)
  }
}