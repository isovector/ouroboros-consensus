{-# LANGUAGE BlockArguments            #-}
{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE NumDecimals               #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Test.Consensus.Genesis.Setup
  ( module Test.Consensus.Genesis.Setup.GenChains
  , forAllGenesisTest
  , forAllGenesisTestIO
  , runGenesisTest
  , runGenesisTest'
  , runGenesisTestIO
  ) where

import Control.Applicative (empty)
import System.Timeout (timeout)
import Test.Consensus.PointSchedule.Shrinking
import GHC.TopHandler
import Control.Monad (replicateM)
import Control.Exception (throw)
import Control.Monad.Class.MonadAsync
  ( AsyncCancelled (AsyncCancelled)
  )
import Control.Monad.IOSim (IOSim, runSimStrictShutdown)
import Control.Tracer (debugTracer, traceWith)
import Data.Maybe (mapMaybe)
import Ouroboros.Consensus.MiniProtocol.ChainSync.Client
  ( ChainSyncClientException (..)
  )
import Ouroboros.Consensus.Util.Condense
import Ouroboros.Consensus.Util.IOLike (Exception, fromException)
import Ouroboros.Network.Driver.Limits
  ( ProtocolLimitFailure (ExceededTimeLimit)
  )
import Test.Consensus.Genesis.Setup.Classifiers
  ( Classifiers (..)
  , ResultClassifiers (..)
  , ScheduleClassifiers (..)
  , classifiers
  , resultClassifiers
  , scheduleClassifiers
  )
import Test.Consensus.Genesis.Setup.GenChains
import Test.Consensus.PeerSimulator.Run
import Test.Consensus.PeerSimulator.StateView
import Test.Consensus.PeerSimulator.Trace
  ( traceLinesWith
  , tracerTestBlock
  )
import Test.Consensus.PointSchedule
import Test.QuickCheck
import Test.Util.Orphans.IOLike ()
import Test.Util.QuickCheck (forAllGenRunShrinkCheck)
import Test.Util.TestBlock (TestBlock)
import Test.Util.Tracer (recordingTracerM, recordingTracerIORef)
import Text.Printf (printf)

-- | Like 'runSimStrictShutdown' but fail when the main thread terminates if
-- there are other threads still running or blocked. If one is trying to follow
-- a strict thread clean-up policy then this helps testing for that.
runSimStrictShutdownOrThrow :: forall a. (forall s. IOSim s a) -> a
runSimStrictShutdownOrThrow action =
  case runSimStrictShutdown action of
    Left e -> throw e
    Right x -> x

-- | Runs the given 'GenesisTest' and 'PointSchedule' and evaluates the given
-- property on the final 'StateView'.
runGenesisTest ::
  SchedulerConfig ->
  GenesisTestFull TestBlock ->
  RunGenesisTestResult
runGenesisTest schedulerConfig genesisTest =
  runSimStrictShutdownOrThrow $ do
    (recordingTracer, getTrace) <- recordingTracerM
    let tracer = if scDebug schedulerConfig then debugTracer else recordingTracer

    traceLinesWith tracer $ prettyGenesisTest prettyPointSchedule genesisTest

    rgtrStateView <- runPointSchedule schedulerConfig genesisTest =<< tracerTestBlock tracer
    traceWith tracer (condense rgtrStateView)
    rgtrTrace <- unlines <$> getTrace

    pure $ RunGenesisTestResult{rgtrTrace, rgtrStateView}

runGenesisTestIO ::
  SchedulerConfig ->
  GenesisTestFull TestBlock ->
  IO RunGenesisTestResult
runGenesisTestIO schedulerConfig genesisTest = do
    (recordingTracer, getTrace) <- recordingTracerIORef
    let tracer = if scDebug schedulerConfig then debugTracer else recordingTracer

    traceLinesWith tracer $ prettyGenesisTest prettyPointSchedule genesisTest

    rgtrStateView <- runPointSchedule schedulerConfig genesisTest =<< tracerTestBlock tracer

    traceWith tracer (condense rgtrStateView)
    rgtrTrace <- unlines <$> getTrace

    pure $ RunGenesisTestResult{rgtrTrace, rgtrStateView}

-- | Variant of 'runGenesisTest' that also takes a property on the final
-- 'StateView' and returns a QuickCheck property. The trace is printed in case
-- of counter-example.
runGenesisTest' ::
  Testable prop =>
  SchedulerConfig ->
  GenesisTestFull TestBlock ->
  (StateView TestBlock -> prop) ->
  Property
runGenesisTest' schedulerConfig genesisTest makeProperty =
  counterexample rgtrTrace $ makeProperty rgtrStateView
 where
  RunGenesisTestResult{rgtrTrace, rgtrStateView} =
    runGenesisTest schedulerConfig genesisTest

replicateMMaybe :: Int -> IO a -> IO [a]
replicateMMaybe n m
  | n <= 0 = do
    putStrLn "✓"
    pure []
  | otherwise = fmap pure m
      -- m >>= \case
      --   Just a -> do
      --     putStr "."
      --     flushStdHandles
      --     as <- replicateMMaybe (n - 1) m
      --     pure $ a : as
      --   Nothing -> do
      --     putStrLn "✗"
      --     pure []

-- | All-in-one helper that generates a 'GenesisTest' and a 'Peers
-- PeerSchedule', runs them with 'runGenesisTest', check whether the given
-- property holds on the resulting 'StateView'.
forAllGenesisTestIO ::
  Testable prop =>
  Gen (GenesisTestFull TestBlock) ->
  SchedulerConfig ->
  (GenesisTestFull TestBlock -> StateView TestBlock -> [GenesisTestFull TestBlock]) ->
  (GenesisTestFull TestBlock -> StateView TestBlock -> prop) ->
  Property
forAllGenesisTestIO generator schedulerConfig shrinker mkProperty =
  forAllGenRunShrinkCheck generator runner (\x y -> [] )
    -- shrinkPeerSchedules x undefined)
    $ \genesisTest mresult -> ioProperty $ do
    let len = 1
    results <- replicateMMaybe len mresult
    let result = head results
    let cls = classifiers genesisTest
        resCls = resultClassifiers genesisTest result
        schCls = scheduleClassifiers genesisTest
        stateView = rgtrStateView result
    pure $
     classify (allAdversariesSelectable cls) "All adversaries have more than k blocks after intersection"
          $ classify
            (allAdversariesForecastable cls)
            "All adversaries have at least 1 forecastable block after intersection"
          $ classify
            (allAdversariesKPlus1InForecast cls)
            "All adversaries have k+1 blocks in forecast window after intersection"
          $ classify (genesisWindowAfterIntersection cls) "Full genesis window after intersection"
          $ classify (adversaryRollback schCls) "An adversary did a rollback"
          $ classify (honestRollback schCls) "The honest peer did a rollback"
          $ classify (allAdversariesEmpty schCls) "All adversaries have empty schedules"
          $ classify (allAdversariesTrivial schCls) "All adversaries have trivial schedules"
          $ tabulate "Adversaries killed by LoP" [printf "%.1f%%" $ adversariesKilledByLoP resCls]
          $ tabulate "Adversaries killed by GDD" [printf "%.1f%%" $ adversariesKilledByGDD resCls]
          $ tabulate "Adversaries killed by Timeout" [printf "%.1f%%" $ adversariesKilledByTimeout resCls]
          $ tabulate "Surviving adversaries" [printf "%.1f%%" $ adversariesSurvived resCls]
          $ counterexample (rgtrTrace result)
          $ (mkProperty genesisTest $ rgtrStateView result) .&&. hasOnlyExpectedExceptions stateView .&&. length results === len
 where
  runner = runGenesisTestIO $ schedulerConfig
  hasOnlyExpectedExceptions StateView{svPeerSimulatorResults} =
    conjoin $
      isExpectedException
        <$> mapMaybe
          (pscrToException . pseResult)
          svPeerSimulatorResults
  isExpectedException exn
    | Just EmptyBucket <- e = true
    | Just DensityTooLow <- e = true
    | Just (ExceededTimeLimit _) <- e = true
    | Just AsyncCancelled <- e = true
    | Just CandidateTooSparse{} <- e = true
    | otherwise =
        counterexample
          ("Encountered unexpected exception: " ++ show exn)
          False
   where
    e :: Exception e => Maybe e
    e = fromException exn
    true = property True

-- | All-in-one helper that generates a 'GenesisTest' and a 'Peers
-- PeerSchedule', runs them with 'runGenesisTest', check whether the given
-- property holds on the resulting 'StateView'.
forAllGenesisTest ::
  Testable prop =>
  Gen (GenesisTestFull TestBlock) ->
  SchedulerConfig ->
  (GenesisTestFull TestBlock -> StateView TestBlock -> [GenesisTestFull TestBlock]) ->
  (GenesisTestFull TestBlock -> StateView TestBlock -> prop) ->
  Property
forAllGenesisTest generator schedulerConfig shrinker mkProperty =
  forAllGenRunShrinkCheck generator runner shrinker' $ \genesisTest result ->
    let cls = classifiers genesisTest
        resCls = resultClassifiers genesisTest result
        schCls = scheduleClassifiers genesisTest
        stateView = rgtrStateView result
     in classify (allAdversariesSelectable cls) "All adversaries have more than k blocks after intersection"
          $ classify
            (allAdversariesForecastable cls)
            "All adversaries have at least 1 forecastable block after intersection"
          $ classify
            (allAdversariesKPlus1InForecast cls)
            "All adversaries have k+1 blocks in forecast window after intersection"
          $ classify (genesisWindowAfterIntersection cls) "Full genesis window after intersection"
          $ classify (adversaryRollback schCls) "An adversary did a rollback"
          $ classify (honestRollback schCls) "The honest peer did a rollback"
          $ classify (allAdversariesEmpty schCls) "All adversaries have empty schedules"
          $ classify (allAdversariesTrivial schCls) "All adversaries have trivial schedules"
          $ tabulate "Adversaries killed by LoP" [printf "%.1f%%" $ adversariesKilledByLoP resCls]
          $ tabulate "Adversaries killed by GDD" [printf "%.1f%%" $ adversariesKilledByGDD resCls]
          $ tabulate "Adversaries killed by Timeout" [printf "%.1f%%" $ adversariesKilledByTimeout resCls]
          $ tabulate "Surviving adversaries" [printf "%.1f%%" $ adversariesSurvived resCls]
          $ counterexample (rgtrTrace result)
          $ mkProperty genesisTest stateView .&&. hasOnlyExpectedExceptions stateView
 where
  runner = runGenesisTest schedulerConfig
  shrinker' gt = shrinker gt . rgtrStateView
  hasOnlyExpectedExceptions StateView{svPeerSimulatorResults} =
    conjoin $
      isExpectedException
        <$> mapMaybe
          (pscrToException . pseResult)
          svPeerSimulatorResults
  isExpectedException exn
    | Just EmptyBucket <- e = true
    | Just DensityTooLow <- e = true
    | Just (ExceededTimeLimit _) <- e = true
    | Just AsyncCancelled <- e = true
    | Just CandidateTooSparse{} <- e = true
    | otherwise =
        counterexample
          ("Encountered unexpected exception: " ++ show exn)
          False
   where
    e :: Exception e => Maybe e
    e = fromException exn
    true = property True
