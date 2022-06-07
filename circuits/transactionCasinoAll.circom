include "../node_modules/circomlib/circuits/poseidon.circom";
include "../node_modules/circomlib/circuits/comparators.circom";
include "../node_modules/circomlib/circuits/gates.circom";
include "../node_modules/circomlib/circuits/mux1.circom";
include "./merkleProof.circom"
include "./keypair.circom"
include "./CasinoReturn.circom"

/*
Utxo structure:
{
    amount,
    pubkey,
    blockNum, //0 means that the utxo is rolled already
    blinding, // random number
}

commitment = hash(amount, pubKey, blockNum, blinding)
nullifier = hash(commitment, merklePath, sign(privKey, commitment, merklePath))
*/

// Universal JoinSplit transaction with nIns inputs and 2 outputs
template TransactionCasinoAll(levels, nIns, nOuts, zeroLeaf) {
    signal input nullifierTreeMerkleRoot;
    signal input rngNumberTreeMerkleRoot; // a merkle tree that contains data Poseidon(blocknumber(252 bits),rngNumber(220 bits)) at each leaf
    // extAmount = external amount used for deposits and withdrawals
    // correct extAmount range is enforced on the smart contract
    // publicAmount = extAmount - fee
    signal input publicAmount;
    signal input extDataHash;
    signal input currentBlockNum;

    // data for casino
    signal private input rngNumber[nIns];

    // assistance variabe that tells which inputs goes to which outputs.
    signal private input InOutAmount[nIns+1][nOuts+1];

    // data for transaction inputs
    signal         input inputNullifier[nIns];
    signal private input inBlockNum[nIns];
    signal private input inAmount[nIns];
    signal private input inPrivateKey[nIns];
    signal private input inBlinding[nIns];
    signal private input inPathIndices[nIns];
    signal private input inPathElements[nIns][levels];

    signal private input rngTreeInPathIndices[nIns];
    signal private input rngTreeInPathElements[nIns][levels];

    // data for transaction outputs
    signal         input outputCommitment[nOuts];
    signal private input outAmount[nOuts];
    signal private input outPubkey[nOuts];
    signal private input outBlockNum[nOuts];
    signal private input outBlinding[nOuts];

    component inKeypair[nIns];
    component inSignature[nIns];
    component inCommitmentHasher[nIns];
    component inNullifierHasher[nIns];
    component inTree[nIns];
    component inCheckNullifierTreeMerkleRoot[nIns];

    component rngTreeRNGBlockNumberHasher[nIns];
    component inTreeRNG[nIns];
    component inCheckRNGTreeMerkleRoot[nIns];

    // verify correctness of transaction inputs
    for (var tx = 0; tx < nIns; tx++) {
        inKeypair[tx] = Keypair();
        inKeypair[tx].privateKey <== inPrivateKey[tx];

        // commitment = hash(amount, pubKey, blinding)
        inCommitmentHasher[tx] = Poseidon(4);
        inCommitmentHasher[tx].inputs[0] <== inAmount[tx];
        inCommitmentHasher[tx].inputs[1] <== inKeypair[tx].publicKey;
        inCommitmentHasher[tx].inputs[2] <== inBlockNum[tx];
        inCommitmentHasher[tx].inputs[3] <== inBlinding[tx];

        // sign(privKey, commitment, merklePath)
        inSignature[tx] = Signature();
        inSignature[tx].privateKey <== inPrivateKey[tx];
        inSignature[tx].commitment <== inCommitmentHasher[tx].out;
        inSignature[tx].merklePath <== inPathIndices[tx];

        // check that nullifier = hash(commitment, merklePath, sign(privKey, commitment, merklePath))
        inNullifierHasher[tx] = Poseidon(3);
        inNullifierHasher[tx].inputs[0] <== inCommitmentHasher[tx].out;
        inNullifierHasher[tx].inputs[1] <== inPathIndices[tx];
        inNullifierHasher[tx].inputs[2] <== inSignature[tx].out;
        inNullifierHasher[tx].out === inputNullifier[tx];

        // Check that the merkle proof is correct
        inTree[tx] = MerkleProof(levels);
        inTree[tx].leaf <== inCommitmentHasher[tx].out;
        inTree[tx].pathIndices <== inPathIndices[tx];
        for (var i = 0; i < levels; i++) {
            inTree[tx].pathElements[i] <== inPathElements[tx][i];
        }

        // check merkle proof only if amount is non-zero
        inCheckNullifierTreeMerkleRoot[tx] = ForceEqualIfEnabled();
        inCheckNullifierTreeMerkleRoot[tx].in[0] <== nullifierTreeMerkleRoot;
        inCheckNullifierTreeMerkleRoot[tx].in[1] <== inTree[tx].root;
        inCheckNullifierTreeMerkleRoot[tx].enabled <== inAmount[tx];

        // Check that the merkle proof is correct for RNG number
        rngTreeRNGBlockNumberHasher[tx] = Poseidon(2);
        rngTreeRNGBlockNumberHasher[tx].inputs[0] <== inBlockNum[tx];
        rngTreeRNGBlockNumberHasher[tx].inputs[1] <== rngNumber[tx];

        inTreeRNG[tx] = MerkleProof(levels);
        inTreeRNG[tx].leaf <== rngTreeRNGBlockNumberHasher[tx].out;
        inTreeRNG[tx].pathIndices <== rngTreeInPathIndices[tx];
        for (var i = 0; i < levels; i++) {
            inTreeRNG[tx].pathElements[i] <== rngTreeInPathElements[tx][i];
        }

        // check RNG merkle proof only if amount is non-zero and blocknum is nonzero
        inCheckRNGTreeMerkleRoot[tx] = ForceEqualIfEnabled();
        inCheckRNGTreeMerkleRoot[tx].in[0] <== rngNumberTreeMerkleRoot;
        inCheckRNGTreeMerkleRoot[tx].in[1] <== inTreeRNG[tx].root;
        inCheckRNGTreeMerkleRoot[tx].enabled <== inAmount[tx] * inBlockNum[tx];

        // We don't need to range check input amounts, since all inputs are valid UTXOs that
        // were already checked as outputs in the previous transaction (or zero amount UTXOs that don't
        // need to be checked either).
    }

    component outCommitmentHasher[nOuts];
    component outAmountCheck[nOuts];

    // verify correctness of transaction outputs
    for (var tx = 0; tx < nOuts; tx++) {

        // commitment = hash(amount, pubKey, blinding)
        outCommitmentHasher[tx] = Poseidon(4);
        outCommitmentHasher[tx].inputs[0] <== outAmount[tx];
        outCommitmentHasher[tx].inputs[1] <== outPubkey[tx];
        outCommitmentHasher[tx].inputs[2] <== outBlockNum[tx];
        outCommitmentHasher[tx].inputs[3] <== outBlinding[tx];
        outCommitmentHasher[tx].out === outputCommitment[tx];

        // Check that amount fits into 248 bits to prevent overflow
        outAmountCheck[tx] = Num2Bits(248);
        outAmountCheck[tx].in <== outAmount[tx];
    }

    component returnCalculator[nIns];
    component muxes[nIns];
    component blockNumComparison[nIns];
    component blockOrs[nIns];
    component blockNots[nIns];
    var inAmountsAfterLottery[nIns];
    // calculate help array that contains current values of the inputs (win amounts if the time has passed and original value otherwise)
    for (var txIn = 0; txIn < nIns; txIn++) {
        returnCalculator[txIn] = CasinoReturn();//todo, mix the output with some hashing dependent on the utxo
        returnCalculator[txIn].ticketPrice <== inAmount[txIn];
        returnCalculator[txIn].rng <== rngNumber[txIn];

        //inBlockNum==0, this is same as 1-0<inBlockNum
        blockNots[txIn] = LessThan(252);
        blockNots[txIn].in[0] <== 0;
        blockNots[txIn].in[1] <== inBlockNum[txIn];
        var not = 1 - blockNots[txIn].out;

        //currentBlockNum <= inBlockNum[txIn];
        blockNumComparison[txIn] = LessEqThan(252);
        blockNumComparison[txIn].in[0] <== currentBlockNum;
        blockNumComparison[txIn].in[1] <== inBlockNum[txIn];

        //currentBlockNum <= inBlockNum; or inBlockNum == 0
        blockOrs[txIn] = OR();
        blockOrs[txIn].a <== not;
        blockOrs[txIn].b <== blockNumComparison[txIn].out;

        //if the block has passed, use winning amount, otherwise the normal value
        muxes[txIn] = Mux1();
        muxes[txIn].c[0] <== returnCalculator[txIn].returnValue;
        muxes[txIn].c[1] <== inAmount[txIn];
        muxes[txIn].s <== blockOrs[txIn].out;
        inAmountsAfterLottery[txIn] = muxes[txIn].out;
    }

    // verify that InOut mapping matches to inAmounts

    //input sums match
    for (var txIn = 0; txIn < nIns; txIn++) {
        var sumIns = 0;
        for (var txOut = 0; txOut < nOuts + 1; txOut++) {
            sumIns += InOutAmount[txIn+1][txOut];
        }
        sumIns === inAmountsAfterLottery[txIn];
    }

    //output sums match
    for (var txOut = 0; txOut < nOuts; txOut++) {
        var sumOuts = 0;
        for (var txIn = 0; txIn < nIns + 1; txIn++) {
            sumOuts += InOutAmount[txIn][txOut+1];
        }
        sumOuts === outAmount[txOut];
    }

    // moving funds from outside to inside has to go throught the casino (blocknum > currentBlockNum)
    component blockNumComps[nOuts];
    for (var txOut = 1; txOut < nOuts + 1; txOut++) {
        var txIn = 0;
        blockNumComps[txOut-1] = LessThan(252);
        blockNumComps[txOut-1].in[0] <== currentBlockNum;
        blockNumComps[txOut-1].in[1] <== outBlockNum[txOut-1];
        blockNumComps[txOut-1].out * InOutAmount[txIn][txOut] === InOutAmount[txIn][txOut];
    }
    //moving won funds inside:  [{inBlockNum<currentBlockNum && (outBlockNum==0 || outBlockNum>currentBlockNum) } || {outBlockNum>inBlockNum && outBlockNum>currentBlockNum} ] || InOutAmount == 0
    component outBlockNumBiggerThanInBlockNum[nIns][nOuts];
    component inBlockNumSmallerThancurrentBlockNum[nIns][nOuts];
    component outBlockNumBiggerThancurrentBlockNum[nIns][nOuts];
    component outBlockNumNonZero[nIns][nOuts];
    component lastOr[nIns][nOuts];
    component ors[nIns][nOuts];
    for (var txOut = 1; txOut < nOuts + 1; txOut++) {
        for (var txIn = 1; txIn < nIns + 1; txIn++) {
            //inBlockNum<currentBlockNum
            inBlockNumSmallerThancurrentBlockNum[txIn-1][txOut-1] = LessThan(252);
            inBlockNumSmallerThancurrentBlockNum[txIn-1][txOut-1].in[0] <== inBlockNum[txIn-1];
            inBlockNumSmallerThancurrentBlockNum[txIn-1][txOut-1].in[1] <== currentBlockNum;

            //outBlockNum==0, this is same as 1-0<outBlockNum
            outBlockNumNonZero[txIn-1][txOut-1] = LessThan(252);
            outBlockNumNonZero[txIn-1][txOut-1].in[0] <== 0;
            outBlockNumNonZero[txIn-1][txOut-1].in[1] <== outBlockNum[txOut-1];
            var not = 1 - outBlockNumNonZero[txIn-1][txOut-1].out;

            //outBlockNum>currentBlockNum
            outBlockNumBiggerThancurrentBlockNum[txIn-1][txOut-1] = LessThan(252);
            outBlockNumBiggerThancurrentBlockNum[txIn-1][txOut-1].in[0] <== currentBlockNum;
            outBlockNumBiggerThancurrentBlockNum[txIn-1][txOut-1].in[1] <== outBlockNum[txOut-1];

            //(outBlockNum==0 || outBlockNum>currentBlockNum)
            ors[txIn-1][txOut-1] = OR();
            ors[txIn-1][txOut-1].a <== not;
            ors[txIn-1][txOut-1].b <== outBlockNumBiggerThancurrentBlockNum[txIn-1][txOut-1].out;

            // inBlockNum>currentBlockNum && (outBlockNum==0 || outBlockNum>currentBlockNum)
            var first = inBlockNumSmallerThancurrentBlockNum[txIn-1][txOut-1].out * ors[txIn-1][txOut-1].out;

            //outBlockNum>inBlockNum && outBlockNum>currentBlockNum
            outBlockNumBiggerThanInBlockNum[txIn-1][txOut-1] = LessThan(252);
            outBlockNumBiggerThanInBlockNum[txIn-1][txOut-1].in[0] <== inBlockNum[txIn-1];
            outBlockNumBiggerThanInBlockNum[txIn-1][txOut-1].in[1] <== outBlockNum[txOut-1];
            var second = outBlockNumBiggerThanInBlockNum[txIn-1][txOut-1].out * outBlockNumBiggerThancurrentBlockNum[txIn-1][txOut-1].out;

            lastOr[txIn-1][txOut-1] = OR();
            lastOr[txIn-1][txOut-1].a <== first;
            lastOr[txIn-1][txOut-1].b <== second;

            lastOr[txIn-1][txOut-1].out*InOutAmount[txIn][txOut] === InOutAmount[txIn][txOut];
        }
    }

    // check that there are no same nullifiers among all inputs
    component sameNullifiers[nIns * (nIns - 1) / 2];
    var index = 0;
    for (var i = 0; i < nIns - 1; i++) {
      for (var j = i + 1; j < nIns; j++) {
          sameNullifiers[index] = IsEqual();
          sameNullifiers[index].in[0] <== inputNullifier[i];
          sameNullifiers[index].in[1] <== inputNullifier[j];
          sameNullifiers[index].out === 0;
          index++;
      }
    }

    // verify amount invariant
    var totalSumOuts = 0;
    for (var txIn = 0; txIn < nIns+1; txIn++) {
        totalSumOuts += InOutAmount[txIn][0];
    }
    var totalSumIns = 0;
    for (var txOut = 0; txOut < nOuts+1; txOut++) {
        totalSumIns += InOutAmount[0][txOut];
    }
    totalSumIns + publicAmount === totalSumOuts;

    // optional safety constraint to make sure extDataHash cannot be changed
    signal extDataSquare <== extDataHash * extDataHash;
}
