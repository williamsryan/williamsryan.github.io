{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Control.Monad
import           Prelude
-- import           System.Exit
import           System.FilePath (replaceExtension, takeDirectory)
import qualified Data.Text as T
-- import qualified Data.Set as S
import qualified System.Process  as Process
import Text.Pandoc (
      WriterOptions (writerExtensions)
    , writerTemplate
    , writerTopLevelDivision
    , writerTableOfContents
    , writerNumberSections
    , writerHTMLMathMethod
    , HTMLMathMethod(MathJax)
    , compileTemplate
    , runPure
    , runWithDefaultPartials
    , readerExtensions
    , writerExtensions
    , pandocExtensions
    )

import Text.Pandoc.Options

import Data.Default (def)

import Hakyll
import Hakyll.Web.Pandoc

-----------------
-- Configuration.
-----------------
config :: Configuration
config = defaultConfiguration {
    destinationDirectory = "docs"
}

-----------------
-- Etc compilers.
-----------------
-- Compile the TOC template and store it in a compiler
-- tocTemplateCompiler :: Compiler Template
-- tocTemplateCompiler = do
--     let tocTemplateStr = "<h2>Table of Contents</h2>\n$toc$\n$body$"
--     compileTemplate "tocTemplate" tocTemplateStr

--------------
-- Entrypoint.
--------------
main :: IO ()
main = hakyllWith config $ do
    -- Static files.
    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    -- JS files.
    match "js/*" $ do
        route   idRoute
        compile copyFileCompiler

    -- Compress CSS into one file.
    match "css/*" $ compile compressCssCompiler
    create ["style.css"] $ do
        route   idRoute
        compile $ do
            csses <- loadAll "css/*.css"
            makeItem $ unlines $ map itemBody csses

    -- match (fromList ["about.rst", "contact.markdown"]) $ do
    --     route   $ setExtension "html"
    --     compile $ pandocCompiler
    --         >>= loadAndApplyTemplate "templates/default.html" defaultContext
    --         >>= relativizeUrls

    -- Render news posts.
    match "news/*" $ do
        route   $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/news.html" defaultContext
            >>= loadAndApplyTemplate "templates/content.html" defaultContext
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    -- News list.
    create ["news.html"] $ do
        route idRoute
        compile $ do
            news <- recentFirst =<< loadAll "news/*"
            let ctx =   listField "news" postCtx (return news) <>
                        defaultContext
            makeItem ""
                >>= loadAndApplyTemplate "templates/news-list.html" ctx
                >>= loadAndApplyTemplate "templates/content.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

    -- Render each and every post (Markdown format).
    match "posts/*" $ do
        route $ setExtension "html"
        compile $ do
            item <- getResourceBody
            toc <- getMetadataField (itemIdentifier item) "toc"
            let ctx = defaultContext
            let tocTemplate =
                    either error id $ either (error . show) id $
                    runPure $ runWithDefaultPartials $
                    compileTemplate "" "<h2>Table of Contents</h2>$toc$\n$body$"
            let writerOptions' = case toc of
                    Just _  -> withTOC { writerTemplate = Just tocTemplate }
                    Nothing -> withoutTOC
            pandocCompilerWith defaultHakyllReaderOptions writerOptions'
                >>= loadAndApplyTemplate "templates/post.html" ctx
                >>= loadAndApplyTemplate "templates/content.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

    -- Render each and every post (LaTeX format).
    -- match "posts/*" $ do
    --     route   $ setExtension "html"
    --     compile $ getResourceString
    --         >>= withItemBody (unixFilter "pandoc" ["-f", "latex", "-t", "html5", "--toc","--mathjax"])
    --         >>= loadAndApplyTemplate "templates/post.html" postCtx
    --         >>= loadAndApplyTemplate "templates/content.html" postCtx
    --         >>= loadAndApplyTemplate "templates/default.html" postCtx
    --         >>= relativizeUrls

    -- Post list.
    create ["posts.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            let ctx =   listField "posts" postCtx (return posts) <>
                        defaultContext
            makeItem ""
                >>= loadAndApplyTemplate "templates/posts.html" ctx
                >>= loadAndApplyTemplate "templates/content.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

    -- Better way of rendering arbitrary dirs (talks, teaching, etc.).
    match (
        "**index.md"
        -- .&&. complement "books/**"
        ) $ do
        route $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/content.html" defaultContext
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    -- Index.
    match "index.html" $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            news <- recentFirst =<< loadAll "news/*"
            let indexCtx =
                    listField "posts" postCtx (return posts) `mappend`
                    listField "news" postCtx (return news) `mappend`
                    defaultContext
            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/content.html" indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    -- Compile templates.
    match "templates/*" $ compile templateCompiler

    -- Render the 404 page, we don't relativize URL's here.
    match "404.html" $ do
        route idRoute
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/content.html" defaultContext
            >>= loadAndApplyTemplate "templates/default.html" defaultContext

    -- CV as PDF.
    match "cv/cv-pdf.tex" $ version "pdf" $ do
        route   $ constRoute "cv.pdf"
        compile $ getResourceString >>= xelatex

    -- Serve book assets from the "books/beautiful-coq" directory.
    match "books/beautiful-coq/**" $ do
        route idRoute
        compile copyFileCompiler

    -- Separate rule for CV.
    match "cv/cv.tex" $ do
        route   $ constRoute "cv/index.html"
        compile $ getResourceString
            >>= withItemBody (unixFilter "pandoc" ["-f", "latex", "-t", "html5"])
            >>= loadAndApplyTemplate "templates/cv.html" postCtx
            >>= loadAndApplyTemplate "templates/default.html" postCtx
            >>= relativizeUrls

    -- Render LaTeX docs as HTML.
    match ("*/*.tex" .&&. complement "cv/*")$ do
        -- route   $ constRoute "cv/index.html"
        compile $ getResourceString
            >>= withItemBody (unixFilter "pandoc" ["-f", "latex", "-t", "html5","--mathjax", "-shell-escape"])
            >>= loadAndApplyTemplate "templates/content.html" postCtx
            >>= loadAndApplyTemplate "templates/default.html" postCtx
            >>= relativizeUrls

--------------------------------------------------------------------------------

--------------
-- Contexts.
--------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext

withTOC :: WriterOptions
withTOC = defaultHakyllWriterOptions{
    writerNumberSections  = True,
    writerTableOfContents = True,
    -- writerTemplate = Just tocTemplate,
    writerHTMLMathMethod = MathJax ""
}

withoutTOC :: WriterOptions
withoutTOC = defaultHakyllWriterOptions{
    writerHTMLMathMethod = MathJax ""
}

---------------
-- LaTeX stuff.
---------------
xelatex :: Item String -> Compiler (Item TmpFile)
xelatex item = do
    TmpFile texPath <- newTmpFile "pdflatex.tex"
    let pdfPath = replaceExtension texPath "pdf"
    unsafeCompiler $ do
        writeFile texPath $ itemBody item
        _ <- Process.system $ unwords [
            "export TEXINPUTS=.:./cv/:",
            "&&",
            "xelatex",
            "-interaction=nonstopmode",
            "-output-directory=" ++ takeDirectory texPath,
            texPath
            ]
        return ()
    makeItem $ TmpFile pdfPath

