{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
#if __GLASGOW_HASKELL__ >= 810
{-# OPTIONS_GHC -Wno-prepositive-qualified-module #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_witherable (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
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
version = Version [0,5] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath




bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/home/sn/.cabal/store/ghc-9.4.8/witherable-0.5-b8991e05bfb1745252feab0e9167d57875b428237bb03876a556bb3d4a53a0af/bin"
libdir     = "/home/sn/.cabal/store/ghc-9.4.8/witherable-0.5-b8991e05bfb1745252feab0e9167d57875b428237bb03876a556bb3d4a53a0af/lib"
dynlibdir  = "/home/sn/.cabal/store/ghc-9.4.8/witherable-0.5-b8991e05bfb1745252feab0e9167d57875b428237bb03876a556bb3d4a53a0af/lib"
datadir    = "/home/sn/.cabal/store/ghc-9.4.8/witherable-0.5-b8991e05bfb1745252feab0e9167d57875b428237bb03876a556bb3d4a53a0af/share"
libexecdir = "/home/sn/.cabal/store/ghc-9.4.8/witherable-0.5-b8991e05bfb1745252feab0e9167d57875b428237bb03876a556bb3d4a53a0af/libexec"
sysconfdir = "/home/sn/.cabal/store/ghc-9.4.8/witherable-0.5-b8991e05bfb1745252feab0e9167d57875b428237bb03876a556bb3d4a53a0af/etc"

getBinDir     = catchIO (getEnv "witherable_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "witherable_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "witherable_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "witherable_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "witherable_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "witherable_sysconfdir") (\_ -> return sysconfdir)



joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
