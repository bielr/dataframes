module Data.Frame.Plugin (plugin) where

import Control.Lens qualified as L
import Control.Monad (when)
import Control.Monad.IO.Class
import Data.Generics.Uniplate.Data qualified as U

import GHC.Data.Bag
import GHC.Data.FastString
import GHC.Data.StringBuffer
import GHC.Driver.Plugins
import GHC.Driver.Session (getDynFlags)
import GHC.Driver.Types
import GHC.Hs
import GHC.Parser
import GHC.Parser.Lexer
import GHC.Parser.PostProcess
import GHC.Types.Name
import GHC.Types.Name.Reader
import GHC.Types.SrcLoc
import GHC.Utils.Error
--import GHC.Hs.Doc


plugin :: Plugin
plugin = defaultPlugin
    { parsedResultAction = parsedPlugin
    , pluginRecompile = purePlugin
    }


parsedPlugin :: [CommandLineOption] -> ModSummary -> HsParsedModule -> Hsc HsParsedModule
parsedPlugin _ _ =
    hpm_moduleL.locatedL.hsmodDeclsL.traverse.locatedL L.%%~ processHsDecl
  where
    hpm_moduleL :: L.Lens' HsParsedModule (Located HsModule)
    hpm_moduleL = L.lens hpm_module (\hpm m -> hpm { hpm_module = m })

    hsmodDeclsL :: L.Lens' HsModule [LHsDecl GhcPs]
    hsmodDeclsL = L.lens hsmodDecls (\hsm ds -> hsm { hsmodDecls = ds })

    locatedL :: L.Traversal' (Located a) a
    locatedL = traverse

    processHsDecl :: HsDecl GhcPs -> Hsc (HsDecl GhcPs)
    processHsDecl = U.transformBiM processHsExpr

    processHsExpr :: HsExpr GhcPs -> Hsc (HsExpr GhcPs)
    processHsExpr = \case
        HsSpliceE NoExtField splice
            | HsQuasiQuote NoExtField splicePoint quoter srcSpan contents <- splice
            , "_row" <- occNameString (occName quoter)
            -> do
                row_e <- parseStringAsLHsExpr srcSpan contents

                let env_name = mkQual varName (fsLit "Data.Frame.TH.Expr", fsLit "env")
                    env_e = HsVar NoExtField (noLoc env_name)
                    br_e = HsBracket NoExtField (ExpBr NoExtField row_e)
                    splice_e = HsApp NoExtField (noLoc env_e) (noLoc br_e)

                return $
                    HsSpliceE NoExtField $
                        HsUntypedSplice NoExtField DollarSplice splicePoint $
                            noLoc (HsPar NoExtField (noLoc splice_e))

        e -> return e


    parseStringAsLHsExpr :: SrcSpan -> FastString -> Hsc (LHsExpr GhcPs)
    parseStringAsLHsExpr srcSpan fstr = do
        let location =
                case srcSpanStart srcSpan of
                    RealSrcLoc rl _ -> rl
                    UnhelpfulLoc bs -> mkRealSrcLoc bs 1 1

        dflags <- getDynFlags

        let strBuffer = stringToStringBuffer (unpackFS fstr)
            parseState = mkPState dflags strBuffer location

        -- pretty much copied from GHC.Driver.Main
        case unP (parseExpression >>= runECP_P) parseState of
            PFailed pst -> do
                handleWarningsThrowErrors (getMessages pst dflags)
            POk pst e -> do
                logWarningsReportErrors (getMessages pst dflags)
                return e


-- Powerful copy & paste from GHC.Driver.Main

getWarnings :: Hsc WarningMessages
getWarnings = Hsc $ \_ w -> return (w, w)

logWarnings :: WarningMessages -> Hsc ()
logWarnings w = Hsc $ \_ w0 -> return ((), w0 `unionBags` w)

-- | log warning in the monad, and if there are errors then
-- throw a SourceError exception.
logWarningsReportErrors :: Messages -> Hsc ()
logWarningsReportErrors (warns,errs) = do
    logWarnings warns
    when (not $ isEmptyBag errs) $ throwErrors errs


-- | Log warnings and throw errors, assuming the messages
-- contain at least one error (e.g. coming from PFailed)
handleWarningsThrowErrors :: Messages -> Hsc a
handleWarningsThrowErrors (warns, errs) = do
    logWarnings warns
    dflags <- getDynFlags
    (wWarns, wErrs) <- warningsToMessages dflags <$> getWarnings
    liftIO $ printBagOfErrors dflags wWarns
    throwErrors (unionBags errs wErrs)
