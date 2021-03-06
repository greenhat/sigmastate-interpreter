package sigmastate.utxo.examples

import sigmastate.Values.{IntConstant, TaggedBox}
import sigmastate._
import sigmastate.helpers.{ErgoProvingInterpreter, SigmaTestingCommons}
import sigmastate.utxo.ErgoBox.R3
import sigmastate.utxo._
import sigmastate.lang.Terms._

class DemurrageExampleSpecification extends SigmaTestingCommons {

  /**
    * Demurrage currency example.
    *
    * The idea is that miners enforce users to combine a guarding script of a user ("regular_script") with a condition
    * that anyone (presumably, a miner) can spend no more "demurrage_cost" amount of tokens from an output of the user
    * after "demurrage_period" blocks since output creation. If the user is relocating the money from the output before
    * that height, the miner can charge according to output lifetime.
    *
    * We assume that it is enforced by a consensus protocol to store height when an input got into a block in the
    * register R3 (if the transaction is not included into the blockchain yet, then R3 contains the current height of
    * the blockchain).
    *
    * (regular_script) ∨
    * (height > (self.R3 + demurrage_period ) ∧ has_output(value >= self.value − demurrage_cost, script = self.script))
    */
  property("Evaluation - Demurrage Example") {
    val demurragePeriod = 100
    val demurrageCost = 2

    //a blockchain node veryfing a block containing a spending transaction
    val verifier = new ErgoInterpreter

    //backer's prover with his private key
    val userProver = new ErgoProvingInterpreter

    val regScript = userProver.dlogSecrets.head.publicImage

    val env = Map(
      "demurragePeriod" -> demurragePeriod,
      "demurrageCost" -> demurrageCost,
      "regScript" -> regScript
    )
    val prop = compile(env,
      """{
        | let c2 = allOf(Array(
        |   HEIGHT >= SELF.R3[Int].value + demurragePeriod,
        |   OUTPUTS.exists(fun (out: Box) = {
        |     out.value >= SELF.value - demurrageCost && out.propositionBytes == SELF.propositionBytes
        |   })
        | ))
        | regScript || c2
        | }
      """.stripMargin).asBoolValue
    val propTree = OR(
      regScript,
      AND(
        GE(Height, Plus(ExtractRegisterAs[SInt.type](Self, R3), IntConstant(demurragePeriod))),
        Exists(Outputs, 21,
          AND(
            GE(ExtractAmount(TaggedBox(21)), Minus(ExtractAmount(Self), IntConstant(demurrageCost))),
            EQ(ExtractScriptBytes(TaggedBox(21)), ExtractScriptBytes(Self))
          )
        )
      )
    )
    prop shouldBe propTree

    val outHeight = 100
    val outValue = 10
    val curHeight = outHeight + demurragePeriod

    //case 1: demurrage time hasn't come yet
    val tx1 = ErgoTransaction(
      IndexedSeq(),
      IndexedSeq(ErgoBox(outValue, prop, additionalRegisters = Map(R3 -> IntConstant(curHeight)))))

    val ctx1 = ErgoContext(
      currentHeight = outHeight + demurragePeriod - 1,
      lastBlockUtxoRoot = AvlTreeData.dummy,
      boxesToSpend = IndexedSeq(),
      spendingTransaction = tx1,
      self = createBox(outValue, prop, additionalRegisters = Map(R3 -> IntConstant(outHeight))))

    //user can spend all the money
    val uProof1 = userProver.prove(prop, ctx1, fakeMessage).get.proof
    verifier.verify(prop, ctx1, uProof1, fakeMessage).get._1 shouldBe true

    //miner can't spend any money
    verifier.verify(prop, ctx1, NoProof, fakeMessage).get._1 shouldBe false

    //case 2: demurrage time has come
    val ctx2 = ErgoContext(
      currentHeight = outHeight + demurragePeriod,
      lastBlockUtxoRoot = AvlTreeData.dummy,
      boxesToSpend = IndexedSeq(),
      spendingTransaction = tx1,
      self = createBox(outValue, prop, additionalRegisters = Map(R3 -> IntConstant(outHeight))))

    //user can spend all the money
    val uProof2 = userProver.prove(prop, ctx1, fakeMessage).get.proof
    verifier.verify(prop, ctx2, uProof2, fakeMessage).get._1 shouldBe true

    //miner can spend "demurrageCost" tokens
    val tx3 = ErgoTransaction(IndexedSeq(),
      IndexedSeq(ErgoBox(outValue - demurrageCost, prop, additionalRegisters = Map(R3 -> IntConstant(curHeight)))))
    val ctx3 = ErgoContext(
      currentHeight = outHeight + demurragePeriod,
      lastBlockUtxoRoot = AvlTreeData.dummy,
      boxesToSpend = IndexedSeq(),
      spendingTransaction = tx3,
      self = createBox(outValue, prop, additionalRegisters = Map(R3 -> IntConstant(outHeight))))


    assert(ctx3.spendingTransaction.outputs.head.propositionBytes sameElements ctx3.self.propositionBytes)

    verifier.verify(prop, ctx3, NoProof, fakeMessage).get._1 shouldBe true

    //miner can't spend more
    val tx4 = ErgoTransaction(IndexedSeq(),
      IndexedSeq(ErgoBox(outValue - demurrageCost - 1, prop, additionalRegisters = Map(R3 -> IntConstant(curHeight)))))
    val ctx4 = ErgoContext(
      currentHeight = outHeight + demurragePeriod,
      lastBlockUtxoRoot = AvlTreeData.dummy,
      boxesToSpend = IndexedSeq(),
      spendingTransaction = tx4,
      self = createBox(outValue, prop, additionalRegisters = Map(R3 -> IntConstant(outHeight))))

    verifier.verify(prop, ctx4, NoProof, fakeMessage).get._1 shouldBe false

    //miner can spend less
    val tx5 = ErgoTransaction(IndexedSeq(),
      IndexedSeq(ErgoBox(outValue - demurrageCost + 1, prop, additionalRegisters = Map(R3 -> IntConstant(curHeight)))))

    val ctx5 = ErgoContext(
      currentHeight = outHeight + demurragePeriod,
      lastBlockUtxoRoot = AvlTreeData.dummy,
      boxesToSpend = IndexedSeq(),
      spendingTransaction = tx5,
      self = createBox(outValue, prop, additionalRegisters = Map(R3 -> IntConstant(outHeight))))

    verifier.verify(prop, ctx5, NoProof, fakeMessage).get._1 shouldBe true
  }
}
