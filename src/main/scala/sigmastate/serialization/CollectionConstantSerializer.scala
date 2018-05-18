package sigmastate.serialization

import com.google.common.primitives.Shorts
import sigmastate.{SByte, SCollection}
import sigmastate.SType.TypeCode
import sigmastate.Values.{CollectionConstant, ByteArrayConstant}
import sigmastate.serialization.OpCodes._
import sigmastate.serialization.Serializer.{Position, Consumed}

object CollectionConstantSerializer extends ValueSerializer[CollectionConstant[SByte.type]] {

  override val opCode: OpCode = CollectionConstantCode
  val typeCode: TypeCode = SCollection.SByteArrayTypeCode

  override def parseBody(bytes: Array[Byte], pos: Position): (CollectionConstant[SByte.type], Consumed) = {
    val length = Shorts.fromByteArray(bytes.slice(pos, pos + 2))
    val consumed = 2 + length
    val array = bytes.slice(pos + 2 , pos + consumed)
    (ByteArrayConstant(array), consumed)
  }

  override def serializeBody(arr: CollectionConstant[SByte.type]): Array[Byte] = {
    val lengthBytes = Shorts.toByteArray(arr.value.length.toShort)
    lengthBytes ++ arr.value
  }
}
