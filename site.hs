{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Control.Monad
import           Prelude         hiding (id)
-- import           System.Exit
import           System.FilePath (replaceExtension, takeDirectory)
import qualified Data.Text as T
import qualified System.Process  as Process
import qualified Text.Pandoc     as Pandoc

import Hakyll

-----------------
-- Configuration.
-----------------
config :: Configuration
config = defaultConfiguration {
    destinationDirectory = "docs"
} 

--------------
-- Entrypoint.
--------------
main :: IO ()
main = hakyllWith config $ do
    -- Static files.
    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    -- Compress CSS into one file.
    match "assets/*.css" $ compile compressCssCompiler
    create ["style.css"] $ do
        route   idRoute
        compile $ do
            csses <- loadAll "assets/*.css"
            makeItem $ unlines $ map itemBody csses

    -- match (fromList ["about.rst", "contact.markdown"]) $ do
    --     route   $ setExtension "html"
    --     compile $ pandocCompiler
    --         >>= loadAndApplyTemplate "templates/default.html" defaultContext
    --         >>= relativizeUrls

    -- Render each and every post.
    match "posts/*" $ do
        route   $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/post.html" defaultContext
            >>= loadAndApplyTemplate "templates/content.html" defaultContext
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    -- Post list.
    create ["posts.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            let ctx =   constField "title" "Posts" <>
                        listField "posts" postCtx (return posts) <>
                        defaultContext
            makeItem ""
                >>= loadAndApplyTemplate "templates/posts.html" ctx
                >>= loadAndApplyTemplate "templates/content.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

    -- Better way of rendering arbitrary dirs (talks, teaching, etc.).
    match "**index.md" $ do
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
            let indexCtx =
                    listField "posts" postCtx (return posts) `mappend`
                    defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/content.html" indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    -- Compile templates.
    match "templates/*" $ compile $ templateCompiler

    -- Render the 404 page, we don't relativize URL's here.
    match "404.html" $ do
        route idRoute
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/content.html" defaultContext
            >>= loadAndApplyTemplate "templates/default.html" defaultContext

    -- CV as PDF.
    -- match "cv.markdown" $ version "pdf" $ do
    --     route   $ setExtension ".pdf"
    --     compile $ do getResourceBody
    --         >>= readPandoc
    --         >>= writeXeTex
    --         >>= loadAndApplyTemplate "templates/cv.tex" defaultContext
    --         >>= xelatex

--------------------------------------------------------------------------------

--------------
-- Contexts.
--------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext
