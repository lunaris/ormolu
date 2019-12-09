{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

-- | Rendering of modules.
module Ormolu.Printer.Meat.Module
  ( p_hsModule,
  )
where

import Control.Monad
import qualified Data.Text as T
import GHC
-- import Ormolu.Imports
import Ormolu.Parser.Pragma
import Ormolu.Printer.Combinators
import Ormolu.Printer.Comments
import Ormolu.Printer.Meat.Common
import Ormolu.Printer.Meat.Declaration
import Ormolu.Printer.Meat.Declaration.Warning
import Ormolu.Printer.Meat.ImportExport
import Ormolu.Printer.Meat.Pragma

import Data.Maybe (fromMaybe)
-- import Ormolu.Parser.CommentStream
import qualified Data.Map.Strict as M

import Ormolu.Utils (getStartLine)

-- import Debug.Trace

-- import Data.Bifunctor

-- | Render a module.
p_hsModule ::
  -- | Shebangs
  [Located String] ->
  -- | Pragmas
  [Pragma] ->
  -- | AST to print
  ParsedSource ->
  R ()
p_hsModule shebangs pragmas (L moduleSpan HsModule {..}) = do
  -- If span of exports in multiline, the whole thing is multiline. This is
  -- especially important because span of module itself always seems to have
  -- length zero, so it's not reliable for layout selection.
  let exportSpans = maybe [] (\(L s _) -> [s]) hsmodExports
      deprecSpan = maybe [] (\(L s _) -> [s]) hsmodDeprecMessage
      spans' = exportSpans ++ deprecSpan ++ [moduleSpan]
  switchLayout spans' $ do
    forM_ shebangs $ \x ->
      located x $ \shebang -> do
        txt (T.pack shebang)
        newline
    spitStackHeader
    newline
    p_pragmas pragmas
    newline
    case hsmodName of
      Nothing -> return ()
      Just hsmodName' -> do
        located hsmodName' $ \name -> do
          forM_ hsmodHaddockModHeader (p_hsDocString Pipe True)
          p_hsmodName name
        forM_ hsmodDeprecMessage $ \w -> do
          breakpoint
          located' p_moduleWarning w
        case hsmodExports of
          Nothing -> return ()
          Just hsmodExports' -> do
            breakpoint
            inci (p_hsmodExports (unLoc hsmodExports'))
        breakpoint
        txt "where"
        newline
    newline

    -- cs <- popImportComments lastLine

    importComments <- getImportComments

  -- traceShow (M.map (fmap unRealSrcSpan) importComments) $

    forM_ hsmodImports $ \x -> located x $ \_ -> do
      let comments = fromMaybe [] $ do
            l <- getStartLine x
            M.lookup l importComments
      withCommentStream comments $
        located' p_hsmodImport x

    -- let importLineSet = E.fromList (mapMaybe getStartLine hsmodImports)
    -- id $ do -- unless (E.null importLineSet)

      -- fileName <- maybe "" (srcLocFile . realSrcSpanStart . getRealSrcSpan)
      --   <$> observeNextComment

      -- This should output (and remove from the comment stream) all
      -- comments that go before the import section.

      -- located (L importSectionSpn ()) $ \() -> traceShow (firstLine, lastLine) $ do

        -- We want to sort imports before printing them, which means that
        -- outputting corresponding comments is trickier and we cannot just use
        -- our familiar 'located' helpers. 'located' picks up and outputs
        -- anything up to current position, so that if the last import becomes
        -- the first after sorting all comments will be dumped before it.
        --
        -- Instead we pop all comments that are within the import section before
        -- we start outputting comments and then we manually match and output
        -- them as we go through the import list.

    newline
    switchLayout (getLoc <$> hsmodDecls) $ do
      p_hsDecls Free hsmodDecls
      newline
      spitRemainingComments
