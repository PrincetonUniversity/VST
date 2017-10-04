import Control.Monad
import Text.ParserCombinators.Parsec as P
import qualified Data.Map as M
import qualified Data.Set as S
import Text.PrettyPrint.HughesPJ

type GR = [(String,S.Set String)]

dependsParser :: Parser GR
dependsParser = do
   ls <- many parseDependLine
   eof
   return ls

parseDependLine :: Parser (String,S.Set String)
parseDependLine = do
   nm <- fname
   string ".vo"
   optional (many (P.char ' '))
   _ <- fname
   string ".glob"
   optional (many (P.char ' '))
   string ":"
   optional (many (P.char ' '))
   deps <- sepBy parseDep (many1 (P.char ' '))
   manyTill (P.char ' ') newline
   let depsSet = S.fromList (filter (/=nm) deps)
   return (nm, depsSet)

parseDep :: Parser String
parseDep = do
   optional (string "./")
   nm <- fname
   (try (string ".vo") <|> string ".v")
   return nm

fname :: Parser String
fname = many1 (alphaNum <|> oneOf "_")

graphDoc :: GR -> Doc
graphDoc gr =
   text "digraph SrcDeps {"
   $+$
     nest 4 (vcat (map docLine gr))
   $+$
   text "}"

docLine :: (String, S.Set String) -> Doc
docLine (nm, deps) | codeFile nm =
  text nm <+> text "[color=blue,shape=note]" <+> docDeps nm (S.toList deps)
docLine (nm, deps) | proofFile nm =
  text nm <+> text "[color=red,shape=oval]" <+> docDeps nm (S.toList deps)

docDeps :: String -> [String] -> Doc
docDeps _ [] = empty
docDeps nm nms = vcat (map ln nms)
  where ln x = text nm <+> text "->" <+> text x <> text ";"

dropFiles = [
  "base", "Coqlib", "Coqlib2", "ClassicalReasoningAboutComputation",
  "Extensionality", "loadpath", "superpose_modelsat",
  "superpose_modelsat_sound", "example", "isolate", "isolate_sound" ]

dropFile = flip elem dropFiles

codeFiles = [
  "redblack", "compare", "variables", "datatypes",
  "superpose", "heapresolve", "veristar",
  "clauses", "isolate",
  "clause_universe", "wellfounded", "fresh"]

codeFile = flip elem codeFiles

proofFile = not . codeFile

mapFst :: (a -> b) -> (a,c) -> (b,c)
mapFst f (x,y) = (f x,y)

mapSnd :: (a -> b) -> (c,a) -> (c,b)
mapSnd f (x,y) = (x,f y)

filterGraph :: GR -> GR
filterGraph = map (mapSnd (S.filter f)) . filter (f . fst)
  where f = not . flip elem dropFiles

main :: IO ()
main = do
  parseFromFile dependsParser ".depend"
    >>= either (fail . show) (return . render . graphDoc . filterGraph)
    >>= putStrLn
