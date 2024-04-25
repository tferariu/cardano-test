{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}


module Contract.MultiSig
    ( State (..)
    , Input (..)
    , Params (..)
 --   , PParams (..)
 --   , CParams (..)
 --   , AParams (..)
 --   , StartParams (..)
 --   , MintParams (..)
 --   , SMSchema
 --   , endpoints
 --   , curSymbol
    , POSIXTime (..)
    ) where


import Control.Lens (makeClassyPrisms)
import Control.Monad (void)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.RWS.Class (asks)
import Data.Map qualified as Map


import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as C
import PlutusTx (ToData)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex)
--import PlutusTx.Prelude ()
import PlutusTx.Prelude --qualified as PlutusTx
import           PlutusTx.AssocMap    (lookup)
--import           PlutusTx.Ratio
--import PlutusTx.Builtins

import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node (
  SlotConfig,
  pSlotConfig,
  posixTimeRangeToContainedSlotRange,
 )
import Cardano.Node.Emulator.Test (testnet)

import Data.Maybe --(fromJust)
import Ledger qualified
import Ledger (Lovelace, PaymentPubKeyHash (unPaymentPubKeyHash), TxId, getCardanoTxId)
import Ledger.Tx.CardanoAPI qualified as C
import Ledger.Typed.Scripts (validatorCardanoAddress)
import Ledger.Typed.Scripts qualified as Scripts
import Plutus.Script.Utils.Scripts --(ValidatorHash, datumHash)
import Plutus.Script.Utils.V2.Contexts (
  ScriptContext (ScriptContext, scriptContextTxInfo),
  TxInfo,
  scriptOutputsAt,
  txInfoValidRange,
  txSignedBy,
 )
import Plutus.Script.Utils.V2.Typed.Scripts --qualified as V2 --HERE!!
import Plutus.Script.Utils.Value --(Value, geq, lt, AssetClass)
import PlutusLedgerApi.V1.Interval qualified as Ival
import PlutusLedgerApi.V2 --(Datum (Datum), OutputDatum(..))
import PlutusLedgerApi.V2.Contexts --(valuePaidTo)
import PlutusLedgerApi.V2.Tx --(OutputDatum (OutputDatum))
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Value --(Lovelace) --(lovelaceValueOf)
-- ???????????????????
import           Data.Aeson           (FromJSON, ToJSON)
import           Data.Text            (Text)
import           GHC.Generics         (Generic)
import           Text.Printf          (printf)
import           Prelude              (Show (..), String)
import qualified Prelude








{-
import           Control.Monad        hiding (fmap)
import qualified Data.Map             as Map

import qualified PlutusCore.Default  as PLC
import PlutusCore.Version  (plcVersion100)
import PlutusTx
import PlutusTx.Lift
import PlutusTx.Prelude
import           PlutusTx.Prelude     hiding (Semigroup(..), unless)
import           PlutusTx.Builtins.Class as C


-- import           Cardano.Node.Emulator.Params (pNetworkId)
-- import qualified Test.QuickCheck.ContractModel  as QCCM

import PlutusLedgerApi.V1.Value
import PlutusLedgerApi.V2
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V2.Contexts
import PlutusLedgerApi.V1.Interval qualified as Ival
-}


minVal :: Integer --Lovelace
minVal = 2000000


type Deadline = Integer



data Label = Holding
           | Collecting Value PaymentPubKeyHash Deadline [PaymentPubKeyHash]
       deriving (Show, Generic)

{-# INLINABLE lEq #-}
lEq :: Label -> Label -> Bool
lEq Holding Holding = True
lEq Holding (Collecting _ _ _ _) = False
lEq (Collecting _ _ _ _) Holding = False
lEq (Collecting v pkh d sigs) (Collecting v' pkh' d' sigs') = v == v' && pkh == pkh' && d == d' && sigs == sigs'


instance Eq Label where
    {-# INLINABLE (==) #-}
    b == c = lEq b c


data State = State
    { label  :: Label
    , tToken :: AssetClass
    } deriving (Show, Generic)

instance Eq State where
    {-# INLINABLE (==) #-}
    b == c = (label b  == label c) &&
             (tToken b == tToken c)


data Input = Propose Value PaymentPubKeyHash Deadline
           | Add PaymentPubKeyHash
           | Pay
           | Cancel
          deriving (Show, Generic)


PlutusTx.unstableMakeIsData ''Label
PlutusTx.makeLift ''Label
PlutusTx.unstableMakeIsData ''Input
PlutusTx.makeLift ''Input
PlutusTx.unstableMakeIsData ''State
PlutusTx.makeLift ''State




{-# INLINABLE query #-}
query :: PaymentPubKeyHash -> [PaymentPubKeyHash] -> Bool
query pkh [] = False
query pkh (x : l') = x == pkh || (query pkh l')

{-# INLINABLE insert #-}
insert :: PaymentPubKeyHash -> [PaymentPubKeyHash] -> [PaymentPubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if x == pkh then x : l' else x : insert pkh l'

{-# INLINABLE count #-}
count :: [PaymentPubKeyHash] -> Integer
count [] = 0
count (x : l) = 1 + count l

data Params = Params {authSigs :: [PaymentPubKeyHash], nr :: Integer}
    deriving (Show, Generic)

PlutusTx.unstableMakeIsData ''Params
PlutusTx.makeLift ''Params




{-# INLINABLE lovelaceValue #-}
-- | A 'Value' containing the given quantity of Lovelace.
lovelaceValue :: Integer -> Value
lovelaceValue = singleton adaSymbol adaToken


{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces v = assetClassValueOf v (AssetClass (adaSymbol, adaToken))
--getLovelace . fromValue


{-# INLINABLE getVal #-}
getVal :: TxOut -> AssetClass -> Integer
getVal ip ac = assetClassValueOf (txOutValue ip) ac




------------------------------------------------------------------------------------------------------------------------------
-- on-chain
------------------------------------------------------------------------------------------------------------------------------


{-# INLINABLE info #-}
-- ?? needed?
info :: ScriptContext -> TxInfo
info ctx = scriptContextTxInfo ctx

{-# INLINABLE ownInput #-}
ownInput :: ScriptContext -> TxOut
ownInput ctx = case findOwnInput ctx of
        Nothing -> traceError "state input missing"
        Just i  -> txInInfoResolved i

{-# INLINABLE ownOutput #-}
ownOutput :: ScriptContext -> TxOut
ownOutput ctx = case getContinuingOutputs ctx of
        [o] -> o
        _   -> traceError "expected exactly one SM output"

{-# INLINABLE smDatum #-}
smDatum :: Maybe Datum -> Maybe State
smDatum md = do
    Datum d <- md
    PlutusTx.fromBuiltinData d

{-# INLINABLE outputDatum #-}
outputDatum :: ScriptContext -> State
outputDatum ctx = case txOutDatum (ownOutput ctx) of
        NoOutputDatum-> traceError "nt"
        OutputDatumHash dh -> case smDatum $ findDatum dh (scriptContextTxInfo ctx) of
            Nothing -> traceError "hs"
            Just d  -> d
        OutputDatum d -> PlutusTx.unsafeFromBuiltinData (getDatum d)

{-# INLINABLE newLabel #-}
newLabel :: ScriptContext -> Label
newLabel ctx = label (outputDatum ctx)

{-# INLINABLE oldValue #-}
oldValue :: ScriptContext -> Value
oldValue ctx = txOutValue (ownInput ctx)

{-# INLINABLE newValue #-}
newValue :: ScriptContext -> Value
newValue ctx = txOutValue (ownOutput ctx)

{-# INLINABLE expired #-}
expired :: Deadline -> TxInfo -> Bool
expired d info = Ival.before ((POSIXTime {getPOSIXTime = d})) (txInfoValidRange info)

{-# INLINABLE checkSigned #-}
checkSigned :: PaymentPubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = txSignedBy (scriptContextTxInfo ctx) (unPaymentPubKeyHash pkh)

{-# INLINABLE checkPayment #-}
checkPayment :: PaymentPubKeyHash -> Value -> TxInfo -> Bool
checkPayment pkh v info = case filter (\i -> (txOutAddress i == (pubKeyHashAddress (unPaymentPubKeyHash pkh)))) (txInfoOutputs info) of
    os -> any (\o -> txOutValue o == (v <> (lovelaceValue minVal))) os


{-# INLINABLE agdaValidator #-}
agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param oldLabel red ctx
  = case oldLabel of
        Collecting v pkh d sigs -> case red of
                                       Propose _ _ _ -> False
                                       Add sig -> checkSigned sig ctx &&
                                                    query sig (authSigs param) &&
                                                      case newLabel ctx of
                                                          Holding -> False
                                                          Collecting v' pkh' d' sigs' -> v == v' &&
                                                                                           pkh ==
                                                                                             pkh'
                                                                                             &&
                                                                                             d == d'
                                                                                               &&
                                                                                               sigs'
                                                                                                 ==
                                                                                                 insert
                                                                                                   sig
                                                                                                   sigs
                                       Pay -> count sigs >= nr param &&
                                                case newLabel ctx of
                                                    Holding -> checkPayment pkh v
                                                                 (scriptContextTxInfo ctx)
                                                                 && oldValue ctx == newValue ctx + v
                                                    Collecting _ _ _ _ -> False
                                       Cancel -> case newLabel ctx of
                                                     Holding -> expired d (scriptContextTxInfo ctx)
                                                     Collecting _ _ _ _ -> False
        Holding -> case red of
                       Propose v pkh d -> geq (oldValue ctx) v &&
                                            case newLabel ctx of
                                                Holding -> False
                                                Collecting v' pkh' d' sigs' -> v == v' &&
                                                                                 pkh == pkh' &&
                                                                                   d == d' &&
                                                                                     sigs' == []
                       Add _ -> False
                       Pay -> False
                       Cancel -> False


--SM Validator
{-# INLINABLE mkValidator #-}
mkValidator :: Params -> State -> Input -> ScriptContext -> Bool
mkValidator param st red ctx =

    traceIfFalse "token missing from input" (getVal (ownInput ctx) (tToken st)  == 1)                 &&
    traceIfFalse "token missing from output" (getVal (ownOutput ctx) (tToken st) == 1)                &&
    traceIfFalse "failed validation" (agdaValidator param (label st) red ctx)


data MultiSig
instance Scripts.ValidatorTypes MultiSig where
  type RedeemerType MultiSig = Input
  type DatumType MultiSig = State


typedValidator :: Params -> TypedValidator MultiSig
typedValidator = go
  where
    go =
      mkTypedValidatorParam @MultiSig
        $$(PlutusTx.compile [||mkValidator||])
        $$(PlutusTx.compile [||wrap||])
    wrap = Scripts.mkUntypedValidator -- @ScriptContext @State @Input

mkAddress :: Params -> Ledger.CardanoAddress
mkAddress = validatorCardanoAddress testnet . typedValidator

---------------------------------------------------

{-
toTxOutValue :: Value -> C.TxOutValue C.BabbageEra
toTxOutValue = either (error . show) C.toCardanoTxOutValue . C.toCardanoValue
-}
toHashableScriptData :: (PlutusTx.ToData a) => a -> C.HashableScriptData
toHashableScriptData = C.unsafeHashableScriptData . C.fromPlutusData . PlutusTx.toData

toTxOutInlineDatum :: (PlutusTx.ToData a) => a -> C.TxOutDatum C.CtxTx C.BabbageEra
toTxOutInlineDatum = C.TxOutDatumInline C.BabbageEraOnwardsBabbage . toHashableScriptData

{-
toValidityRange
  :: SlotConfig
  -> Ival.Interval POSIXTime
  -> (C.TxValidityLowerBound C.BabbageEra, C.TxValidityUpperBound C.BabbageEra)
toValidityRange slotConfig =
  either (error . show) id . C.toCardanoValidityRange . posixTimeRangeToContainedSlotRange slotConfig
-}

-- propose add pay cancel!
{-



proposeSM :: forall w s. PParams -> Contract w s Text ()
proposeSM pp = do
    sm   <- findStateMachineOutput (pParam pp) (pToken pp)
    case sm of
        Nothing -> throwError "SM output not found"
        Just (oref, dto, st) -> do
                logInfo @String "proposing something"
                let pkh   = pPkh pp
                    val   = pVal pp
                    d     = pDeadline pp
                    param = pParam pp
                let st' = st { label = Collecting val pkh d [] }
                let v       = decoratedTxOutPlutusValue dto
                    lookups = Constraints.unspentOutputs (Map.singleton oref dto)                                      <>
                              Constraints.plutusV2OtherScript (stateMachineValidator param)                            <>
                              Constraints.typedValidatorLookups (typedSMValidator param)

                    tx'     = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toBuiltinData $ (Propose val pkh d))    <>
                              Constraints.mustPayToTheScriptWithDatumInTx st' v
                ledgerTx' <- submitTxConstraintsWith @SM lookups tx'
                void $ awaitTxConfirmed $ getCardanoTxId ledgerTx'
                logInfo @String "proposed"
                Contract.logInfo @String $ printf "proposed in %s" (show st)
                Contract.logInfo @String $ printf "proposed to %s" (show st')




mkProposeTx
  :: (E.MonadEmulator m)
  => Params
  -> Value
  -> PaymentPubKeyHash
  -> Deadline
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkProposeTx params val pkh d tt = do
  let smAddr = mkAddress params
  unspentOutputs <- E.utxosAt scAddr
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange

  smUnspentOutputs =
        Map.keys $
          Map.filter (\(C.TxOut _aie tov _tod _rs) -> 
            (assetClassValueOf (C.fromCardanoTxOutValue tov) tt == 1) $
            C.unUTxO unspentOutputs

  case smUnspentOutputs of 
    [] -> throwError $ E.CustomError $ show "no contract"
    [(C.TxOut aie tov tod rs)] -> 
        let
            validityRange = toValidityRange slotConfig $ Interval.from $ current
            txOut = C.TxOut smAddr tov tod C.ReferenceScriptNone

    [] -> throwError $ E.CustomError $ show "more than 1 contract"
  



  if current >= escrowDeadline escrow
    then throwError $ E.CustomError $ show (RedeemFailed DeadlinePassed)
    else
      if C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue (C.unUTxO unspentOutputs))
        `lt` targetTotal escrow
        then throwError $ E.CustomError $ show (RedeemFailed NotEnoughFundsAtAddress)
        else
          let
            validityRange = toValidityRange slotConfig $ Interval.to $ escrowDeadline escrow - 1000
            txOuts = map mkTxOutput (escrowTargets escrow)
            witnessHeader =
              C.toCardanoTxInScriptWitnessHeader
                (Ledger.getValidator <$> Scripts.vValidatorScript (typedValidator escrow))
            redeemer = toHashableScriptData Redeem
            witness =
              C.BuildTxWith $
                C.ScriptWitness C.ScriptWitnessForSpending $
                  witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
            txIns = (,witness) <$> Map.keys (C.unUTxO unspentOutputs)
            utx =
              E.emptyTxBodyContent
                { C.txIns = txIns
                , C.txOuts = txOuts
                , C.txValidityLowerBound = fst validityRange
                , C.txValidityUpperBound = snd validityRange
                }
           in
            pure (C.CardanoBuildTx utx, unspentOutputs)
-}



-- Thread Token
{-# INLINABLE mkPolicy #-}
mkPolicy :: Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
mkPolicy addr oref tn () ctx = traceIfFalse "UTxO not consumed"   hasUTxO                  &&
                          traceIfFalse "wrong amount minted" checkMintedAmount
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    cs :: CurrencySymbol
    cs = ownCurrencySymbol ctx

    hasUTxO :: Bool
    hasUTxO = any (\i -> txInInfoOutRef i == oref) $ txInfoInputs info

    checkMintedAmount :: Bool
    checkMintedAmount = case flattenValue (txInfoMint info) of
        [(_, tn', amt)] -> tn' == tn && amt == 1
        _               -> False

{-
policy :: Params -> TxOutRef -> TokenName -> MintingPolicy
policy param oref tn = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| \addr' oref' tn' ->  mkPolicy addr' oref' tn' ||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode (mkAddress param)
    `PlutusTx.applyCode`
    PlutusTx.liftCode oref
    `PlutusTx.applyCode`
    PlutusTx.liftCode tn
-}
{-

{-# INLINEABLE mkUntypedValidator #-}
mkUntypedValidator :: Params -> BuiltinData -> BuiltinData -> BuiltinData -> ()
mkUntypedValidator param datum redeemer ctx =
  check
    ( mkValidator
        param
        (PlutusTx.unsafeFromBuiltinData datum)
        (PlutusTx.unsafeFromBuiltinData redeemer)
        (PlutusTx.unsafeFromBuiltinData ctx)
    )

smValidatorScript ::
  Params ->
  CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
smValidatorScript params =
  ($$(PlutusTx.compile [||mkUntypedValidator||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 params)
-}

{-
curSymbol :: Params -> TxOutRef -> TokenName -> CurrencySymbol
curSymbol param oref tn = Scripts.scriptCurrencySymbol $ policy param oref tn
-}

------------------------------------------------------------------------



{-

data SM
instance Scripts.ValidatorTypes SM where
    type instance RedeemerType SM = Input
    type instance DatumType SM = State


typedSMValidator :: Params -> Scripts.TypedValidator SM
typedSMValidator param = Scripts.mkTypedValidator @SM
    ($$(PlutusTx.compile [|| mkValidator ||])
       `PlutusTx.applyCode` PlutusTx.liftCode param)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.mkUntypedValidator @ScriptContext @State @Input



stateMachineValidator :: Params -> Validator
stateMachineValidator param = Scripts.validatorScript (typedSMValidator param)

stateMachineAddress :: Params -> Address
stateMachineAddress param = mkValidatorAddress (stateMachineValidator param)


-- Thread Token
{-# INLINABLE mkPolicy #-}
mkPolicy :: Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
mkPolicy addr oref tn () ctx = traceIfFalse "UTxO not consumed"   hasUTxO                  &&
                          traceIfFalse "wrong amount minted" checkMintedAmount
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    cs :: CurrencySymbol
    cs = ownCurrencySymbol ctx

    hasUTxO :: Bool
    hasUTxO = any (\i -> txInInfoOutRef i == oref) $ txInfoInputs info

    checkMintedAmount :: Bool
    checkMintedAmount = case flattenValue (txInfoMint info) of
        [(_, tn', amt)] -> tn' == tn && amt == 1
        _               -> False


policy :: Params -> TxOutRef -> TokenName -> Scripts.MintingPolicy
policy param oref tn = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| \addr' oref' tn' -> Scripts.mkUntypedMintingPolicy $ mkPolicy addr' oref' tn' ||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode (stateMachineAddress param)
    `PlutusTx.applyCode`
    PlutusTx.liftCode oref
    `PlutusTx.applyCode`
    PlutusTx.liftCode tn

curSymbol :: Params -> TxOutRef -> TokenName -> CurrencySymbol
curSymbol param oref tn = Scripts.scriptCurrencySymbol $ policy param oref tn


{-# INLINABLE mkP2 #-}
mkP2 :: () -> ScriptContext -> Bool
mkP2 _ _ = True

pol2 :: Scripts.MintingPolicy
pol2 = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| Scripts.mkUntypedMintingPolicy mkP2 ||])

cs2 :: CurrencySymbol
cs2 = Scripts.scriptCurrencySymbol $ pol2
-}


------------------------------------------------------------------------------------------------------------------------------
-- off-chain
------------------------------------------------------------------------------------------------------------------------------
{-

findStateMachineOutput :: Params -> AssetClass -> Contract w s Text (Maybe (TxOutRef, DecoratedTxOut, State))
findStateMachineOutput param tt = do

    networkId <- pNetworkId <$> getParams
    let stateMachineCAddress = Scripts.validatorCardanoAddress networkId (typedSMValidator param)

    utxos <- utxosAt $ stateMachineCAddress
    return $ do

        (oref, dto) <- find (\x -> assetClassValueOf (decoratedTxOutPlutusValue (snd x)) tt == 1) $ Map.toList utxos
        return (oref, dto, (g dto))

  where
    g :: DecoratedTxOut -> State
    g dto = case dto of
              x@(ScriptDecoratedTxOut {}) -> case _decoratedTxOutScriptDatum x of
                  (dh, dfq) -> case dfq of
                      DatumInline dat -> PlutusTx.unsafeFromBuiltinData (getDatum dat)
                      DatumInBody dat -> PlutusTx.unsafeFromBuiltinData (getDatum dat)
                      DatumUnknown -> traceError "wrong datum type"
                  _ -> traceError "wrong datum type"
              _ -> traceError "wrong datum type"



data StartParams = StartParams
    { sAddress        :: CardanoAddress
    , sTokenName      :: TokenName
    , sParams         :: Params
    , sValue          :: Value
    } deriving (Show, Generic)

startSM :: forall w s. StartParams -> Contract w s Text ()
startSM sp = do

    utxos <- utxosAt $ sAddress sp

    case Map.keys utxos of
        []       -> Contract.logError @String "no utxo found"
        oref : _ -> do
            let tn      = sTokenName sp
            	cs      = curSymbol (sParams sp) oref tn

            let val     = singleton cs tn 1
                v       = lovelaceValueOf minVal <> val <> sValue sp

            let tok = AssetClass (cs, tn)

            let st = State
                     { label  = Holding
                     , tToken = tok
                     }


                lookups = Constraints.plutusV2MintingPolicy (policy (sParams sp) oref tn)    <>
                          Constraints.unspentOutputs utxos              <>
                          Constraints.typedValidatorLookups (typedSMValidator (sParams sp))

                tx      = Constraints.mustMintValue val                 <>
                          Constraints.mustSpendPubKeyOutput oref        <>
                          Constraints.mustPayToTheScriptWithDatumInTx st v

            ledgerTx <- submitTxConstraintsWith @SM lookups tx
            void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
            Contract.logInfo @String $ printf "forged with %s" (show st)
            Contract.logInfo @String $ printf "forged with %s" (show (sParams sp))







addSig :: PubKeyHash -> Label -> Label
addSig _ Holding = Holding
addSig sig (Collecting a b c sigs) = (Collecting a b c (insert sig sigs))

data AParams = AParams  ----FIX TOMOROROW
    { aToken           :: AssetClass
    , aParam           :: Params
    , aSig             :: PubKeyHash
    } deriving (Show, Generic)

addSM :: forall w s. AParams -> Contract w s Text ()
addSM ap = do


    sm   <- findStateMachineOutput (aParam ap) (aToken ap)

    case sm of
        Nothing -> throwError "SM output not found"
        Just (oref, dto, st) -> do

                logInfo @String "adding signature"

                let sig   = aSig ap
                    param = aParam ap

                let st' = st { label = addSig sig (label st) }


                let v       = decoratedTxOutPlutusValue dto


                    lookups = Constraints.unspentOutputs (Map.singleton oref dto)                                      <>
                              Constraints.plutusV2OtherScript (stateMachineValidator param)                            <>
                              Constraints.typedValidatorLookups (typedSMValidator param)

                    tx'     = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toBuiltinData $ (Add sig))    <>
                              Constraints.mustPayToTheScriptWithDatumInTx st' v                                        <>
                              Constraints.mustBeSignedBy sig

                ledgerTx' <- submitTxConstraintsWith @SM lookups tx'
                void $ awaitTxConfirmed $ getCardanoTxId ledgerTx'
                logInfo @String "adding"
                Contract.logInfo @String $ printf "added for %s" (show st')


getV :: Label -> Value
getV Holding = mempty
getV (Collecting v b c d) = v

getPkh :: Label -> PubKeyHash
getPkh Holding = "9a36b319e1265478782ebadd43e007f16492726a5f5795380316ae17" -- PubKeyHash { unPaymentPubKeyHash = "9a36b319e1265478782ebadd43e007f16492726a5f5795380316ae17" }
getPkh (Collecting a pkh c d) = pkh

data CParams = CParams
    { cToken           :: AssetClass
    , cParam           :: Params
    } deriving (Show, Generic)

paySM :: forall w s. CParams -> Contract w s Text ()
paySM cp = do


    sm   <- findStateMachineOutput (cParam cp) (cToken cp)

    case sm of
        Nothing -> throwError "SM output not found"
        Just (oref, dto, st) -> do

                logInfo @String "paying"

                let param = cParam cp
                    aux = lovelaceValueOf minVal

                let st' = st { label = Holding }
                    val = getV (label st)
                    pkh = getPkh (label st)


                let v       = decoratedTxOutPlutusValue dto - val


                    lookups = Constraints.unspentOutputs (Map.singleton oref dto)                                      <>
                              Constraints.plutusV2OtherScript (stateMachineValidator param)                            <>
                              Constraints.typedValidatorLookups (typedSMValidator param)

                    tx'     = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toBuiltinData $ Pay)    <>
                              Constraints.mustPayToTheScriptWithDatumInTx st' v                                        <>
                              Constraints.mustPayToPubKey pkh (val <> aux)

                Contract.logInfo @String $ printf "paying from %s" (show st)
                Contract.logInfo @String $ printf "from amount %s" (show (decoratedTxOutPlutusValue dto))
                Contract.logInfo @String $ printf "paying %s" (show val)
                Contract.logInfo @String $ printf "paying??? %s" (show (inv val))
                Contract.logInfo @String $ printf "paying to %s" (show st')
                Contract.logInfo @String $ printf "making %s" (show v)

                ledgerTx' <- submitTxConstraintsWith @SM lookups tx'
                void $ awaitTxConfirmed $ getCardanoTxId ledgerTx'
                logInfo @String "paid"
                Contract.logInfo @String $ printf "paid for %s" (show st')



cancelSM :: forall w s. CParams -> Contract w s Text ()
cancelSM cp = do

    sm   <- findStateMachineOutput (cParam cp) (cToken cp)

    case sm of
        Nothing -> throwError "SM output not found"
        Just (oref, dto, st) -> do

                logInfo @String "cancelling"

                let param = cParam cp
                    aux = lovelaceValueOf minVal

                let st' = st { label = Holding }


                let v       = decoratedTxOutPlutusValue dto


                    lookups = Constraints.unspentOutputs (Map.singleton oref dto)                                      <>
                              Constraints.plutusV2OtherScript (stateMachineValidator param)                            <>
                              Constraints.typedValidatorLookups (typedSMValidator param)

                    tx'     = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toBuiltinData $ Cancel)    <>
                    	      Constraints.mustValidateInTimeRange (Interval.interval (POSIXTime {getPOSIXTime = 123456}) (POSIXTime {getPOSIXTime = 12345678}))  <>
                    --	      Constraints.mustValidateInTimeRange (Interval.interval 1 1234) <>
                              Constraints.mustPayToTheScriptWithDatumInTx st' v

                ledgerTx' <- submitTxConstraintsWith @SM lookups tx'
                void $ awaitTxConfirmed $ getCardanoTxId ledgerTx'
                logInfo @String "cancel"
                Contract.logInfo @String $ printf "cancel from %s" (show st)
                Contract.logInfo @String $ printf "cancel to %s" (show st')

{-
data PParams = PParams
    { pToken           :: AssetClass
    , pParam           :: Param
    , pVal             :: Value
    , pPkh             :: PubKeyHash
    , pDeadline        :: Integer
    } deriving (Show, Generic)

proposeSM :: forall w s. PParams -> Contract w s Text ()
proposeSM pp = do

    pkh  <- Contract.ownFirstPaymentPubKeyHash
    sm   <- findStateMachineOutput (pToken pp) (pParam pp)

    case sm of
        Nothing -> throwError "SM output not found"
        Just (oref, dto, st) -> do

                logInfo @String "proposing a value"

                let v       = decoratedTxOutPlutusValue dto
                let st' = st { label = Collecting (pVal pp) (pVal pp) (pDeadline pp) [] }


                    lookups = Constraints.unspentOutputs (Map.singleton oref dto)                                      <>
                              Constraints.plutusV2OtherScript (stateMachineValidator)                                  <>
                              Constraints.typedValidatorLookups (typedSMValidator)

                    tx'     = Constraints.mustSpendScriptOutput oref (Redeemer $ (Propose (pVal pp) (pVal pp) (pDeadline pp) ))      <>
                              Constraints.mustPayToTheScriptWithDatumInTx st' v                                        <>
                              Constraints.mustBeSignedBy pkh

                ledgerTx' <- submitTxConstraintsWith @SM lookups tx'
                void $ awaitTxConfirmed $ getCardanoTxId ledgerTx'
                logInfo @String "toggled"
                Contract.logInfo @String $ printf "toggle for %s" (show st')
-}
{-
data DParams = DParams
    { oToken           :: AssetClass
    , ok               :: Bool
    } deriving (Show, Generic)

toggleSM :: forall w s. DParams -> Contract w s Text ()
toggleSM dp = do

    pkh  <- Contract.ownFirstPaymentPubKeyHash
    sm   <- findStateMachineOutput (oToken dp)

    case sm of
        Nothing -> throwError "SM output not found"
        Just (oref, dto, st) -> do

                logInfo @String "toggling from one to another"

                let st' = if (shape st) == Square then st {shape = Circle}
                  	  	          else if (shape st) == Circle then st {shape = Square}
                			                       else st -- ?? throwerror

                let v       = decoratedTxOutPlutusValue dto

                    inp     = if (ok dp) then Toggle else Other

                    lookups = Constraints.unspentOutputs (Map.singleton oref dto)                                      <>
                              Constraints.plutusV2OtherScript (stateMachineValidator)                                  <>
                              Constraints.typedValidatorLookups (typedSMValidator)

                    tx'     = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toBuiltinData $ inp)      <>
                              Constraints.mustPayToTheScriptWithDatumInTx st' v                                        <>
                              Constraints.mustBeSignedBy pkh

                ledgerTx' <- submitTxConstraintsWith @SM lookups tx'
                void $ awaitTxConfirmed $ getCardanoTxId ledgerTx'
                logInfo @String "toggled"
                Contract.logInfo @String $ printf "toggle for %s" (show st')


     -}



data MintParams = MintParams
    { mTokenName      :: TokenName
    , mamt            :: Integer
    } deriving (Show, Generic)

mintG :: forall w s. MintParams -> Contract w s Text ()
mintG mp = do

    	    pkh <- Contract.ownFirstPaymentPubKeyHash

            let tn      = mTokenName  mp
            	cs      = cs2

            let val     = singleton cs tn (mamt mp)
                v       = lovelaceValueOf minVal <> val


            let lookups = Constraints.plutusV2MintingPolicy (pol2)

                tx      = Constraints.mustMintValue val                 <>
                          Constraints.mustPayToPubKey pkh v

            ledgerTx <- submitTxConstraintsWith @SM lookups tx
            void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
            Contract.logInfo @String $ printf "forged with %s" (show cs)



type SMSchema = Endpoint "start" StartParams .\/ Endpoint "propose" PParams .\/ Endpoint "add" AParams .\/ Endpoint "cancel" CParams .\/ Endpoint "pay" CParams .\/ Endpoint "mint" MintParams

endpoints :: Contract () SMSchema Text ()
endpoints = awaitPromise (start `select` propose `select` pay `select` add `select` cancel `select` mint) >> endpoints
  where
    start    = endpoint @"start"    startSM
    propose  = endpoint @"propose"  proposeSM
    add      = endpoint @"add"      addSM
    pay      = endpoint @"pay"      paySM
    cancel   = endpoint @"cancel"   cancelSM
    mint     = endpoint @"mint"     mintG

-}
