{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
#if __GLASGOW_HASKELL__ >= 810
{-# OPTIONS_GHC -Wno-prepositive-qualified-module #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_text_iso8601 (
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
version = Version [0,1,1] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath




bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/home/sn/.cabal/store/ghc-9.4.8/text-iso8601-0.1.1-1eb1ba992edb14b53f8c2ff3086d7cd2177e53d384015d3c67cd6c312dd006bf/bin"
libdir     = "/home/sn/.cabal/store/ghc-9.4.8/text-iso8601-0.1.1-1eb1ba992edb14b53f8c2ff3086d7cd2177e53d384015d3c67cd6c312dd006bf/lib"
dynlibdir  = "/home/sn/.cabal/store/ghc-9.4.8/text-iso8601-0.1.1-1eb1ba992edb14b53f8c2ff3086d7cd2177e53d384015d3c67cd6c312dd006bf/lib"
datadir    = "/home/sn/.cabal/store/ghc-9.4.8/text-iso8601-0.1.1-1eb1ba992edb14b53f8c2ff3086d7cd2177e53d384015d3c67cd6c312dd006bf/share"
libexecdir = "/home/sn/.cabal/store/ghc-9.4.8/text-iso8601-0.1.1-1eb1ba992edb14b53f8c2ff3086d7cd2177e53d384015d3c67cd6c312dd006bf/libexec"
sysconfdir = "/home/sn/.cabal/store/ghc-9.4.8/text-iso8601-0.1.1-1eb1ba992edb14b53f8c2ff3086d7cd2177e53d384015d3c67cd6c312dd006bf/etc"

getBinDir     = catchIO (getEnv "text_iso8601_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "text_iso8601_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "text_iso8601_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "text_iso8601_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "text_iso8601_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "text_iso8601_sysconfdir") (\_ -> return sysconfdir)



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
