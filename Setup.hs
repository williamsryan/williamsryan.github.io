--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Data.Monoid (mappend)
import           Hakyll
--------------------------------------------------------------------------------

-- Configuration stuff to get this working on GitHub Pages.
config :: Configuration
config = defaultConfiguration {
    destinationDirectory = "docs"
}  

main :: IO ()
main = hakyllWith config $ do
    -- Static files.
    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    -- Compress CSS into one file.
    match "css/*" $ compile compressCssCompiler
    create ["style.css"] $ do
        route   idRoute
        compile $ do
            csses <- loadAll "css/*.css"
            makeItem $ unlines $ map itemBody csses

    match (fromList ["about.rst", "contact.markdown"]) $ do
        route   $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    match "posts/*" $ do
        route $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/post.html"    postCtx
            >>= loadAndApplyTemplate "templates/default.html" postCtx
            >>= relativizeUrls

    create ["archive.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            let archiveCtx =
                    listField "posts" postCtx (return posts) `mappend`
                    constField "title" "Archives"            `mappend`
                    defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
                >>= loadAndApplyTemplate "templates/default.html" archiveCtx
                >>= relativizeUrls

    -- Index.
    match "index.html" $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            let indexCtx =
                    listField "posts" postCtx (return posts) `mappend`
                    defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    -- Read templates.
    match "templates/*" $ compile templateBodyCompiler

    -- CV as PDF.
    -- match "cv.markdown" $ version "pdf" $ do
    --     route   $ setExtension ".pdf"
    --     compile $ do getResourceBody
    --         >>= readPandoc
    --         >>= writeXeTex
    --         >>= loadAndApplyTemplate "templates/cv.tex" defaultContext
    --         >>= xelatex

--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext
