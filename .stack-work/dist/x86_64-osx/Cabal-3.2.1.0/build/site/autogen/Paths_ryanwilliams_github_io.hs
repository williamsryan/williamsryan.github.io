{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_ryanwilliams_github_io (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/ryanwilliams/git/ryanwilliams.github.io/.stack-work/install/x86_64-osx/0a79fc275225a0ea1a42a54efacf32b82ce041c09a0104a75f0a64aaafd13f17/8.10.4/bin"
libdir     = "/Users/ryanwilliams/git/ryanwilliams.github.io/.stack-work/install/x86_64-osx/0a79fc275225a0ea1a42a54efacf32b82ce041c09a0104a75f0a64aaafd13f17/8.10.4/lib/x86_64-osx-ghc-8.10.4/ryanwilliams-github-io-0.1.0.0-L74K4ytDWSC2S2v261sJOW-site"
dynlibdir  = "/Users/ryanwilliams/git/ryanwilliams.github.io/.stack-work/install/x86_64-osx/0a79fc275225a0ea1a42a54efacf32b82ce041c09a0104a75f0a64aaafd13f17/8.10.4/lib/x86_64-osx-ghc-8.10.4"
datadir    = "/Users/ryanwilliams/git/ryanwilliams.github.io/.stack-work/install/x86_64-osx/0a79fc275225a0ea1a42a54efacf32b82ce041c09a0104a75f0a64aaafd13f17/8.10.4/share/x86_64-osx-ghc-8.10.4/ryanwilliams-github-io-0.1.0.0"
libexecdir = "/Users/ryanwilliams/git/ryanwilliams.github.io/.stack-work/install/x86_64-osx/0a79fc275225a0ea1a42a54efacf32b82ce041c09a0104a75f0a64aaafd13f17/8.10.4/libexec/x86_64-osx-ghc-8.10.4/ryanwilliams-github-io-0.1.0.0"
sysconfdir = "/Users/ryanwilliams/git/ryanwilliams.github.io/.stack-work/install/x86_64-osx/0a79fc275225a0ea1a42a54efacf32b82ce041c09a0104a75f0a64aaafd13f17/8.10.4/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "ryanwilliams_github_io_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "ryanwilliams_github_io_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "ryanwilliams_github_io_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "ryanwilliams_github_io_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "ryanwilliams_github_io_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "ryanwilliams_github_io_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
