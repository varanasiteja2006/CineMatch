# VARANASI TEJA 24MID0085
required_pkgs <- c("shiny", "shinydashboard", "DT", "plotly", "dplyr",
                   "tidyr", "data.table", "randomForest", "rpart")
to_install <- required_pkgs[!vapply(required_pkgs, requireNamespace,
                                    logical(1), quietly = TRUE)]
if (length(to_install)) install.packages(to_install)

suppressPackageStartupMessages({
  library(shiny)
  library(shinydashboard)
  library(DT)
  library(plotly)
  library(dplyr)
  library(tidyr)
})


DATA_PATH <- "C:/Users/cmsri/OneDrive/Desktop/movies.csv"

fix_enc <- function(x) {
  x <- as.character(x)
  bad <- !is.na(x) & grepl("\u00C3|\u00C2", x)
  if (any(bad)) {
    y <- suppressWarnings(iconv(x[bad], from = "UTF-8", to = "CP1252"))
    Encoding(y) <- "UTF-8"
    ok <- !is.na(y) & validUTF8(y)
    x[bad][ok] <- y[ok]
  }
  x
}

parse_list <- function(x) {
  lapply(as.character(x), function(s) {
    if (is.na(s)) return(character(0))
    m <- regmatches(s, gregexpr("\"[^\"]*\"|'[^']*'", s))[[1]]
    if (length(m)) {
      m <- substr(m, 2, nchar(m) - 1)
    } else {
      m <- trimws(strsplit(gsub("\\[|\\]", "", s), ",")[[1]])
    }
    m[nzchar(m)]
  })
}

load_movies <- function(path) {
  df <- data.table::fread(path, encoding = "UTF-8", data.table = FALSE,
                          na.strings = c("", "NA", "N/A", "nan", "NaN"),
                          fill = TRUE)
  names(df) <- tolower(trimws(gsub("\\s+", "_", names(df))))
  req <- c("title", "year", "genre", "rating")
  miss <- setdiff(req, names(df))
  if (length(miss)) stop("Dataset is missing required column(s): ",
                         paste(miss, collapse = ", "))
  for (col in c("runtime", "certificate", "director", "stars",
                "metascore", "votes", "gross"))
    if (!col %in% names(df)) df[[col]] <- NA
  
  num <- function(x) suppressWarnings(as.numeric(gsub("[^0-9.]", "", as.character(x))))
  
  dl <- parse_list(fix_enc(df$director))
  sl <- parse_list(fix_enc(df$stars))
  director_main <- vapply(dl, function(v) if (length(v)) v[1] else NA_character_, "")
  cast <- mapply(function(s, d) {
    v <- if (length(s)) s else d[-1]
    if (length(v)) paste(v, collapse = "; ") else NA_character_
  }, sl, dl, USE.NAMES = FALSE)
  
  genre <- trimws(as.character(df$genre))
  genre <- gsub("\\s*,\\s*", ", ", genre)
  genre[is.na(genre) | genre == ""] <- "Unknown"
  
  cert <- trimws(as.character(df$certificate))
  cert[cert == ""] <- NA
  
  out <- data.frame(
    title         = trimws(fix_enc(df$title)),
    year          = num(df$year),
    runtime       = num(df$runtime),
    certificate   = cert,
    genre         = genre,
    director_main = director_main,
    cast          = cast,
    rating        = num(df$rating),
    metascore     = num(df$metascore),
    votes         = num(df$votes),
    gross         = num(df$gross),
    stringsAsFactors = FALSE
  )
  out <- out %>%
    filter(!is.na(title), !is.na(rating), !is.na(year),
           year >= 1880, year <= 2100) %>%
    distinct(title, year, .keep_all = TRUE)
  out$decade <- floor(out$year / 10) * 10
  out$id <- seq_len(nrow(out))
  out
}


build_features <- function(df) {
  genres <- sort(setdiff(unique(unlist(strsplit(df$genre, ", ", fixed = TRUE))),
                         c("", "Unknown")))
  gstr <- paste0(", ", df$genre, ",")
  G <- matrix(unlist(lapply(genres, function(g)
    as.numeric(grepl(paste0(", ", g, ","), gstr, fixed = TRUE)))),
    nrow = nrow(df), dimnames = list(NULL, genres))
  
  zs <- function(x) {
    x[is.na(x)] <- median(x, na.rm = TRUE)
    x[is.na(x)] <- 0
    s <- sd(x)
    if (is.na(s) || s == 0) rep(0, length(x)) else (x - mean(x)) / s
  }
  num <- cbind(year = zs(df$year), runtime = zs(df$runtime),
               rating = zs(df$rating), votes = zs(log1p(df$votes))) * 0.5
  
  cert <- df$certificate
  cert[is.na(cert)] <- "Unrated"
  top <- names(sort(table(cert), decreasing = TRUE))
  top <- top[seq_len(min(8, length(top)))]
  cert[!cert %in% top] <- "Other"
  C <- model.matrix(~ 0 + factor(cert)) * 0.5
  
  X <- cbind(G * 2, num, C)           # genres carry the most weight
  nr <- sqrt(rowSums(X^2)); nr[nr == 0] <- 1
  list(genres = genres, G = G, X = X, Xn = X / nr)
}

#   MACHINE-LEARNING MODELS (predict movie rating)

ml_frame <- function(d, genres, cert_levels, med) {
  imp <- function(x, m) ifelse(is.na(x), m, x)
  gstr <- paste0(", ", gsub("\\s*,\\s*", ", ", d$genre), ",")
  G <- matrix(unlist(lapply(genres, function(g)
    as.numeric(grepl(paste0(", ", g, ","), gstr, fixed = TRUE)))),
    nrow = nrow(d), dimnames = list(NULL, paste0("g_", make.names(genres))))
  cert <- as.character(d$certificate)
  cert[is.na(cert) | cert == ""] <- "Unrated"
  cert[!cert %in% cert_levels] <- "Other"
  out <- data.frame(
    year        = imp(d$year, med$year),
    runtime     = imp(d$runtime, med$runtime),
    log_votes   = log1p(imp(d$votes, med$votes)),
    has_meta    = as.numeric(!is.na(d$metascore)),
    metascore   = imp(d$metascore, med$metascore),
    log_gross   = log1p(imp(d$gross, med$gross)),
    certificate = factor(cert, levels = cert_levels)
  )
  cbind(out, as.data.frame(G))
}

train_models <- function(df, genres) {
  set.seed(42)
  tab <- sort(table(df$certificate[!is.na(df$certificate)]), decreasing = TRUE)
  cert_levels <- unique(c(names(tab)[seq_len(min(8, length(tab)))], "Unrated", "Other"))
  m0 <- function(v) if (is.na(v)) 0 else v
  med <- list(year = m0(median(df$year, na.rm = TRUE)),
              runtime = m0(median(df$runtime, na.rm = TRUE)),
              votes = m0(median(df$votes, na.rm = TRUE)),
              metascore = m0(median(df$metascore, na.rm = TRUE)),
              gross = m0(median(df$gross, na.rm = TRUE)))
  
  mf <- ml_frame(df, genres, cert_levels, med)
  mf$rating <- df$rating
  n <- nrow(mf)
  test_idx  <- sample.int(n, max(2, round(0.2 * n)))
  train_idx <- setdiff(seq_len(n), test_idx)
  train <- mf[train_idx, ]; test <- mf[test_idx, ]
  rf_train <- if (nrow(train) > 15000) train[sample.int(nrow(train), 15000), ] else train
  
  rf   <- randomForest::randomForest(rating ~ ., data = rf_train, ntree = 100,
                                     nodesize = 5, importance = TRUE)
  lmod <- lm(rating ~ ., data = train)
  tree <- rpart::rpart(rating ~ ., data = train,
                       control = rpart::rpart.control(cp = 0.002, maxdepth = 8))
  
  p_rf   <- predict(rf, test)
  p_lm   <- suppressWarnings(predict(lmod, test))
  p_tree <- predict(tree, test)
  metric <- function(a, p) c(RMSE = sqrt(mean((a - p)^2)), MAE = mean(abs(a - p)),
                             R2 = 1 - sum((a - p)^2) / sum((a - mean(a))^2))
  metrics <- data.frame(
    Model = c("Random Forest", "Linear Regression", "Decision Tree"),
    rbind(metric(test$rating, p_rf), metric(test$rating, p_lm),
          metric(test$rating, p_tree)))
  metrics[, 2:4] <- round(metrics[, 2:4], 3)
  
  imp <- randomForest::importance(rf)[, "%IncMSE"]
  imp_df <- data.frame(Feature = gsub("^g_", "Genre: ", names(imp)),
                       Importance = as.numeric(imp), stringsAsFactors = FALSE)
  imp_df <- imp_df[order(-imp_df$Importance), ]
  
  pred_all <- pmin(10, pmax(1, predict(rf, mf)))
  
  list(rf = rf, lm = lmod, tree = tree, metrics = metrics, imp = imp_df,
       test_actual = test$rating, test_pred = p_rf, test_n = nrow(test),
       train_n = nrow(train), cert_levels = cert_levels, med = med,
       genres = genres, pred_all = as.numeric(pred_all))
}


fmt_time <- function(s) {
  if (is.null(s) || is.na(s)) return("-")
  neg <- s < 0; s <- round(abs(s))
  txt <- if (s < 60) paste0(s, " s") else if (s < 3600)
    paste0(s %/% 60, " min ", s %% 60, " s") else
      paste0(s %/% 3600, " h ", (s %% 3600) %/% 60, " min")
  if (neg) paste0("-", txt) else txt
}

pl_style <- function(p) {
  p %>% layout(paper_bgcolor = "rgba(0,0,0,0)", plot_bgcolor = "rgba(0,0,0,0)",
               font = list(family = "Segoe UI, Arial, sans-serif")) %>%
    config(displaylogo = FALSE)
}

RED <- "#E50914"; DARK <- "#221f1f"

empty_log <- function() {
  data.frame(No = integer(), Time = character(), Mode = character(),
             Pick = character(), Search_sec = numeric(), Manual_sec = numeric(),
             Saved_sec = numeric(), stringsAsFactors = FALSE)
}

movie_cards <- function(r) {
  tagList(lapply(seq_len(nrow(r)), function(i) {
    x <- r[i, ]
    div(class = "movie-card",
        div(class = "rank", i),
        div(class = "mc-body",
            h4(paste0(x$title, " (", x$year, ")")),
            div(class = "mc-meta",
                span(class = "badge-r", paste0("\u2605 ", x$rating)),
                span(x$genre),
                if (!is.na(x$runtime)) span(paste0(x$runtime, " min")),
                if (!is.na(x$certificate)) span(class = "cert", x$certificate)),
            if (!is.na(x$director_main)) p(class = "mc-dir", tags$b("Director: "), x$director_main),
            if (!is.na(x$cast)) p(class = "mc-cast", tags$b("Cast: "), x$cast),
            p(class = "mc-why", icon("lightbulb"), " ", x$why)),
        div(class = "mc-score",
            div(class = "pct", paste0(x$match, "%")),
            div(class = "lbl", "match"),
            div(class = "ml", paste0("ML predicted \u2605 ", round(x$ml_pred, 1)))))
  }))
}


css <- "
.skin-black .main-header .logo{background:#141414;color:#E50914;font-weight:800;letter-spacing:1px;border-bottom:0}
.skin-black .main-header .logo:hover{background:#141414}
.skin-black .main-header .navbar{background:#141414;border-bottom:1px solid #2a2a2a}
.skin-black .main-sidebar{background:#141414}
.skin-black .sidebar-menu>li.active>a,.skin-black .sidebar-menu>li:hover>a{border-left-color:#E50914;background:#1f1f1f;color:#fff}
.skin-black .sidebar-menu>li>.treeview-menu{background:#1b1b1b}
.skin-black .sidebar a{color:#d0d0d0}
.content-wrapper,.right-side{background:#f4f5f7}
.box.box-danger{border-top-color:#E50914}
.box.box-solid.box-danger>.box-header{background:#b20710;background-color:#b20710}
.box.box-solid.box-danger{border:1px solid #b20710}
.side-controls{padding:10px 15px;color:#bbb;font-size:12px}
.side-controls .form-control,.side-controls .btn{font-size:12px}
.side-controls label{color:#bbb;font-weight:500}
.hero{background:linear-gradient(120deg,#141414 0%,#3a0a0d 60%,#E50914 140%);color:#fff;border-radius:12px;padding:34px 36px;margin-bottom:18px}
.hero h1{margin:0 0 8px 0;font-weight:800;letter-spacing:.5px}
.hero p{font-size:16px;max-width:900px;opacity:.92;margin:0}
.step{background:#fff;border-radius:10px;padding:16px;box-shadow:0 2px 8px rgba(0,0,0,.06);height:150px}
.step .n{display:inline-block;width:30px;height:30px;border-radius:50%;background:#E50914;color:#fff;text-align:center;line-height:30px;font-weight:700;margin-bottom:8px}
.movie-card{display:flex;align-items:center;background:#fff;border-radius:10px;padding:16px 18px;margin-bottom:14px;box-shadow:0 2px 8px rgba(0,0,0,.08);border-left:5px solid #E50914}
.movie-card .rank{font-size:30px;font-weight:800;color:#E50914;width:52px}
.movie-card .mc-body{flex:1;padding-right:12px}
.movie-card h4{margin:0 0 6px 0;font-weight:700}
.mc-meta span{display:inline-block;margin-right:8px;color:#666;font-size:13px}
.badge-r{background:#221f1f;color:#f5c518!important;padding:1px 8px;border-radius:10px;font-weight:700}
.cert{border:1px solid #aaa;border-radius:3px;padding:0 5px}
.mc-dir,.mc-cast{margin:4px 0 0 0;color:#444;font-size:13px}
.mc-why{margin:8px 0 0 0;color:#8a1118;font-size:13px}
.mc-score{text-align:center;min-width:110px;border-left:1px solid #eee;padding-left:14px}
.mc-score .pct{font-size:30px;font-weight:800;color:#E50914;line-height:1}
.mc-score .lbl{text-transform:uppercase;font-size:11px;color:#888;letter-spacing:1px}
.mc-score .ml{font-size:11px;color:#666;margin-top:6px}
.empty{background:#fff;border:2px dashed #ddd;border-radius:10px;padding:50px;text-align:center;color:#888;font-size:16px}
.time-banner{background:#e8f6ec;border-left:5px solid #1e9e4a;padding:12px 16px;border-radius:6px;margin-bottom:14px;color:#14532d;font-size:15px}
.small-note{color:#777;font-size:12px}
"

ui <- dashboardPage(
  skin = "black",
  dashboardHeader(title = span(icon("film"), " CineMatch"), titleWidth = 250),
  dashboardSidebar(
    width = 250,
    sidebarMenu(
      id = "tabs",
      menuItem("Home", tabName = "home", icon = icon("home")),
      menuItem("Recommend Movies", tabName = "recommend", icon = icon("film")),
      menuItem("Similar Movies", tabName = "similar", icon = icon("clone")),
      menuItem("Data Analysis", icon = icon("chart-bar"),
               menuSubItem("Data Explorer", tabName = "explorer"),
               menuSubItem("Ratings & Genres", tabName = "ratings"),
               menuSubItem("Trends Over Time", tabName = "trends"),
               menuSubItem("Directors & Stars", tabName = "people"),
               menuSubItem("Correlations & Box Office", tabName = "corr")),
      menuItem("ML Models", icon = icon("robot"),
               menuSubItem("Model Performance", tabName = "ml_perf"),
               menuSubItem("Rating Predictor", tabName = "ml_pred")),
      menuItem("Time Saved", tabName = "timesaved", icon = icon("stopwatch")),
      menuItem("About", tabName = "about", icon = icon("info-circle"))
    ),
    hr(style = "border-color:#2a2a2a"),
    div(class = "side-controls",
        fileInput("file", "Load dataset (CSV / TSV)",
                  accept = c(".csv", ".tsv", ".txt")),
        sliderInput("baseline", "Typical manual search time (min)",
                    min = 5, max = 60, value = 18, step = 1),
        div(class = "small-note", "Used as the 'without CineMatch' benchmark."))
  ),
  dashboardBody(
    tags$head(tags$style(HTML(css))),
    tabItems(
      # ---------------------------------------------------------- HOME
      tabItem("home",
              div(class = "hero",
                  h1(icon("film"), " CineMatch"),
                  p("Stop scrolling, start watching. CineMatch learns your taste from the movies and genres you like, ",
                    "combines a content-based similarity engine with a Random Forest rating model, and hands you a short list ",
                    "of movies you will enjoy - then tells you how much search time you saved.")),
              fluidRow(
                valueBoxOutput("vb_movies", 3), valueBoxOutput("vb_genres", 3),
                valueBoxOutput("vb_avg", 3), valueBoxOutput("vb_saved", 3)),
              fluidRow(
                column(3, div(class = "step", div(class = "n", "1"), h4("Tell us your taste"),
                              p("Pick movies you loved and your favourite genres."))),
                column(3, div(class = "step", div(class = "n", "2"), h4("Similarity engine"),
                              p("Cosine similarity compares genres, era, runtime, rating and popularity."))),
                column(3, div(class = "step", div(class = "n", "3"), h4("ML prediction"),
                              p("A Random Forest predicts quality and re-ranks the matches."))),
                column(3, div(class = "step", div(class = "n", "4"), h4("Watch & save time"),
                              p("See your top picks and the minutes saved vs. endless scrolling.")))),
              br(),
              fluidRow(
                box(width = 6, title = "Movies released per decade", status = "danger",
                    solidHeader = TRUE, plotlyOutput("home_decade", height = 300)),
                box(width = 6, title = "Most common genres", status = "danger",
                    solidHeader = TRUE, plotlyOutput("home_genre", height = 300)))
      ),
      # ---------------------------------------------------- RECOMMEND
      tabItem("recommend",
              fluidRow(
                box(width = 4, title = "Your taste profile", status = "danger", solidHeader = TRUE,
                    selectizeInput("liked", "Movies you liked (type to search)", choices = NULL,
                                   multiple = TRUE, options = list(maxOptions = 50, placeholder = "e.g. The Dark Knight")),
                    selectInput("fav_genres", "Favourite genres", choices = NULL, multiple = TRUE),
                    sliderInput("yr", "Release year", min = 1900, max = 2030,
                                value = c(1900, 2030), sep = ""),
                    sliderInput("min_rating", "Minimum IMDb rating", min = 1, max = 10, value = 6.5, step = 0.1),
                    sliderInput("max_rt", "Maximum runtime (min)", min = 60, max = 300, value = 300),
                    selectInput("certs", "Certificate (leave empty for any)", choices = NULL, multiple = TRUE),
                    radioButtons("style", "Recommendation style",
                                 choices = c("Balanced", "Taste-first", "Quality-first"), inline = TRUE),
                    sliderInput("n_rec", "How many movies?", min = 3, max = 20, value = 5, step = 1),
                    actionButton("go", "Recommend", icon = icon("magic"),
                                 class = "btn-danger btn-lg", width = "100%")),
                column(8,
                       uiOutput("rec_banner"),
                       uiOutput("rec_cards")))
      ),
      # ------------------------------------------------------ SIMILAR
      tabItem("similar",
              fluidRow(
                box(width = 4, title = "Find movies like...", status = "danger", solidHeader = TRUE,
                    selectizeInput("sim_movie", "Pick a movie", choices = NULL,
                                   options = list(maxOptions = 50, placeholder = "Search a title")),
                    sliderInput("n_sim", "How many?", min = 3, max = 20, value = 5),
                    actionButton("go_sim", "Find similar", icon = icon("search"),
                                 class = "btn-danger btn-lg", width = "100%"),
                    br(), br(),
                    div(class = "small-note", "Similarity uses genres, era, runtime, certificate, rating and popularity, ",
                        "with bonus points for the same director and shared cast.")),
                column(8, uiOutput("sim_banner"), uiOutput("sim_cards")))
      ),
      # -------------------------------------------------- DATA EXPLORER
      tabItem("explorer",
              fluidRow(
                box(width = 8, title = "Missing values (%) per column", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_missing", height = 260)),
                box(width = 4, title = "Dataset summary", status = "danger", solidHeader = TRUE,
                    tableOutput("tbl_summary"))),
              fluidRow(
                box(width = 12, title = "Browse the data", status = "danger", solidHeader = TRUE,
                    downloadButton("dl_data", "Download filtered rows (CSV)"), br(), br(),
                    DTOutput("tbl_data")))
      ),
      # ------------------------------------------------ RATINGS & GENRES
      tabItem("ratings",
              fluidRow(
                box(width = 6, title = "Distribution of IMDb ratings", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_hist", height = 320)),
                box(width = 6, title = "Movies per genre (top 15)", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_genre_count", height = 320))),
              fluidRow(
                box(width = 6, title = "Rating spread by genre (top 12)", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_genre_box", height = 340)),
                box(width = 6, title = "Average rating by genre (min. 10 movies)", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_genre_avg", height = 340))),
              fluidRow(
                box(width = 12, title = "Certificates", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_cert", height = 280)))
      ),
      # ---------------------------------------------------------- TRENDS
      tabItem("trends",
              fluidRow(box(width = 12, status = "danger",
                           sliderInput("trend_years", "Year range", min = 1900, max = 2030,
                                       value = c(1900, 2030), sep = "", width = "100%"))),
              fluidRow(
                box(width = 6, title = "Movies per year", status = "danger", solidHeader = TRUE,
                    plotlyOutput("p_peryear", height = 300)),
                box(width = 6, title = "Average rating & metascore by decade", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_decade_rating", height = 300))),
              fluidRow(
                box(width = 6, title = "Average runtime by decade", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_runtime", height = 300)),
                box(width = 6, title = "Rating vs votes (log scale, sample)", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_votes_scatter", height = 300))),
              fluidRow(
                box(width = 12, title = "IMDb rating vs Metascore (sample)", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_meta_scatter", height = 320)))
      ),
      # ---------------------------------------------------------- PEOPLE
      tabItem("people",
              fluidRow(box(width = 12, status = "danger",
                           sliderInput("min_movies", "Minimum number of movies", min = 2, max = 15,
                                       value = 3, width = "100%"))),
              fluidRow(
                box(width = 6, title = "Top directors by average rating", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_dir_avg", height = 420)),
                box(width = 6, title = "Most prolific directors", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_dir_count", height = 420))),
              fluidRow(
                box(width = 6, title = "Top actors by average rating", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_act_avg", height = 420)),
                box(width = 6, title = "Most frequent actors", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_act_count", height = 420)))
      ),
      # ----------------------------------------------------- CORRELATION
      tabItem("corr",
              fluidRow(
                box(width = 6, title = "Correlation matrix", status = "danger", solidHeader = TRUE,
                    plotlyOutput("p_corr", height = 380)),
                box(width = 6, title = "Top 15 grossing movies (USD millions)", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_gross_top", height = 380))),
              fluidRow(
                box(width = 6, title = "Runtime distribution", status = "danger", solidHeader = TRUE,
                    plotlyOutput("p_runtime_hist", height = 300)),
                box(width = 6, title = "Top 15 most-voted movies", status = "danger", solidHeader = TRUE,
                    plotlyOutput("p_votes_top", height = 300)))
      ),
      # --------------------------------------------------------- ML PERF
      tabItem("ml_perf",
              fluidRow(valueBoxOutput("vb_best", 3), valueBoxOutput("vb_rmse", 3),
                       valueBoxOutput("vb_r2", 3), valueBoxOutput("vb_split", 3)),
              fluidRow(
                box(width = 5, title = "Model comparison (hold-out test set)", status = "danger",
                    solidHeader = TRUE, tableOutput("tbl_metrics"),
                    div(class = "small-note", "Models predict a movie's IMDb rating from year, runtime, certificate, ",
                        "genres, votes, metascore and gross. Lower RMSE / MAE and higher R\u00B2 are better."),
                    plotlyOutput("p_rmse", height = 230)),
                box(width = 7, title = "Actual vs predicted rating (Random Forest)", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_avp", height = 440))),
              fluidRow(
                box(width = 7, title = "Feature importance (Random Forest, %IncMSE)", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_imp", height = 400)),
                box(width = 5, title = "Prediction errors", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_resid", height = 400)))
      ),
      # --------------------------------------------------------- ML PRED
      tabItem("ml_pred",
              fluidRow(
                box(width = 4, title = "Describe a movie", status = "danger", solidHeader = TRUE,
                    numericInput("p_year", "Release year", value = 2020, min = 1880, max = 2100),
                    numericInput("p_runtime", "Runtime (min)", value = 120, min = 30, max = 400),
                    selectInput("p_cert", "Certificate", choices = c("Unrated")),
                    selectInput("p_genres", "Genres", choices = NULL, multiple = TRUE),
                    numericInput("p_votes", "Expected votes", value = 100000, min = 0),
                    numericInput("p_meta", "Metascore (0 = unknown)", value = 0, min = 0, max = 100),
                    numericInput("p_gross", "Gross, USD millions (0 = unknown)", value = 0, min = 0),
                    actionButton("go_pred", "Predict rating", icon = icon("bolt"),
                                 class = "btn-danger btn-lg", width = "100%")),
                column(8,
                       fluidRow(valueBoxOutput("vb_p_rf", 4), valueBoxOutput("vb_p_lm", 4),
                                valueBoxOutput("vb_p_tree", 4)),
                       uiOutput("pred_verdict")))
      ),
      # ------------------------------------------------------ TIME SAVED
      tabItem("timesaved",
              fluidRow(valueBoxOutput("vb_n", 3), valueBoxOutput("vb_avgsave", 3),
                       valueBoxOutput("vb_totalsave", 3), valueBoxOutput("vb_pct", 3)),
              fluidRow(
                box(width = 6, title = "Manual search vs CineMatch (minutes per search)", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_compare", height = 300)),
                box(width = 6, title = "Cumulative time saved (minutes)", status = "danger",
                    solidHeader = TRUE, plotlyOutput("p_cum", height = 300))),
              fluidRow(
                box(width = 5, title = "Savings projection", status = "danger", solidHeader = TRUE,
                    numericInput("per_month", "Movies I pick per month", value = 12, min = 1),
                    uiOutput("projection"),
                    div(class = "small-note", br(),
                        "How it is measured: the timer starts when you first change a setting for a search and stops ",
                        "when the recommendation appears. The manual benchmark is the slider in the sidebar ",
                        "(default 18 min, a commonly quoted average for browsing streaming apps).")),
                box(width = 7, title = "Search history", status = "danger", solidHeader = TRUE,
                    DTOutput("tbl_log"), br(),
                    actionButton("reset_log", "Reset history", icon = icon("trash"))))
      ),
      # ----------------------------------------------------------- ABOUT
      tabItem("about",
              box(width = 12, title = "About CineMatch", status = "danger", solidHeader = TRUE,
                  h4("Problem"),
                  p("People spend more time scrolling through streaming catalogues than watching. CineMatch shortens that search."),
                  h4("Method"),
                  tags$ul(
                    tags$li(tags$b("Data preparation: "), "text-encoding repair, list-column parsing (director / cast), numeric clean-up, missing-value handling."),
                    tags$li(tags$b("Content-based filtering: "), "each movie becomes a vector (genres, year, runtime, rating, votes, certificate). Your taste profile is the average of the movies you liked plus your favourite genres; cosine similarity ranks every other movie."),
                    tags$li(tags$b("Machine learning: "), "a Random Forest (compared with Linear Regression and a Decision Tree) predicts each movie's rating. The predicted quality and a popularity score are blended with similarity to form the final match score."),
                    tags$li(tags$b("Time saved: "), "measured search time vs. a configurable manual-browsing benchmark.")),
                  h4("Final score"),
                  p("match = w1 x similarity + w2 x ML predicted rating + w3 x popularity. The weights depend on the recommendation style you choose."),
                  h4("Tech"), p("R, Shiny, shinydashboard, plotly, DT, randomForest, rpart, dplyr, tidyr, data.table."))
      )
    )
  )
)

#  8. SERVER

server <- function(input, output, session) {
  
  rv <- reactiveValues(t0 = NULL, log = empty_log())
  recs <- reactiveVal(NULL)
  sims <- reactiveVal(NULL)
  
  # ---------------------------------------------- load + features + ML
  bundle <- reactive({
    path <- if (!is.null(input$file)) input$file$datapath else DATA_PATH
    validate(need(file.exists(path),
                  paste0("Dataset not found at '", DATA_PATH,
                         "'. Edit DATA_PATH at the top of app.R or load a file from the sidebar.")))
    err <- NULL
    withProgress(message = "Starting CineMatch", value = 0, {
      setProgress(0.1, detail = "Reading dataset")
      df <- tryCatch(load_movies(path), error = function(e) { err <<- conditionMessage(e); NULL })
      validate(need(!is.null(df), paste("Could not read the dataset:", err)))
      validate(need(nrow(df) >= 30, "The dataset needs at least 30 valid rows."))
      setProgress(0.3, detail = "Building features")
      f <- build_features(df)
      setProgress(0.5, detail = "Training ML models (one-time)")
      m <- train_models(df, f$genres)
      df$ml_pred <- m$pred_all
      rng <- range(df$ml_pred)
      df$ml_n <- (df$ml_pred - rng[1]) / max(1e-9, diff(rng))
      lv <- log1p(df$votes); lv[is.na(lv)] <- min(lv, na.rm = TRUE)
      df$pop_n <- (lv - min(lv)) / max(1e-9, diff(range(lv)))
      setProgress(1)
    })
    list(df = df, genres = f$genres, G = f$G, X = f$X, Xn = f$Xn, model = m)
  })
  
  genres_long <- reactive({
    bundle()$df %>% select(id, title, rating, year, genre) %>%
      separate_rows(genre, sep = ", ") %>%
      filter(genre != "", genre != "Unknown")
  })
  
  cast_long <- reactive({
    bundle()$df %>% select(title, rating, cast) %>% filter(!is.na(cast)) %>%
      separate_rows(cast, sep = "; ") %>% filter(cast != "")
  })
  
  # --------------------------------------------- initialise inputs
  observeEvent(bundle(), {
    b <- bundle(); df <- b$df
    lab <- setNames(as.character(df$id), paste0(df$title, " (", df$year, ")"))
    updateSelectizeInput(session, "liked", choices = lab, server = TRUE)
    updateSelectizeInput(session, "sim_movie", choices = lab, server = TRUE)
    updateSelectInput(session, "fav_genres", choices = b$genres)
    yr <- range(df$year)
    updateSliderInput(session, "yr", min = yr[1], max = yr[2], value = yr)
    updateSliderInput(session, "trend_years", min = yr[1], max = yr[2], value = yr)
    rt <- range(df$runtime, na.rm = TRUE)
    if (all(is.finite(rt)))
      updateSliderInput(session, "max_rt", min = floor(rt[1]), max = ceiling(rt[2]), value = ceiling(rt[2]))
    updateSelectInput(session, "certs", choices = sort(unique(na.omit(df$certificate))))
    updateSelectInput(session, "p_cert", choices = b$model$cert_levels, selected = "Unrated")
    updateSelectInput(session, "p_genres", choices = b$genres)
  })
  
  # --------------------------------------------- search timer + log
  observeEvent(list(input$liked, input$fav_genres, input$yr, input$min_rating,
                    input$max_rt, input$certs, input$style, input$sim_movie),
               { if (is.null(rv$t0)) rv$t0 <- Sys.time() }, ignoreInit = TRUE)
  
  log_search <- function(mode, pick) {
    el <- if (is.null(rv$t0)) 3 else max(1, as.numeric(difftime(Sys.time(), rv$t0, units = "secs")))
    man <- input$baseline * 60
    rv$log <- rbind(rv$log, data.frame(
      No = nrow(rv$log) + 1, Time = format(Sys.time(), "%H:%M:%S"), Mode = mode,
      Pick = pick, Search_sec = round(el, 1), Manual_sec = man,
      Saved_sec = round(man - el, 1), stringsAsFactors = FALSE))
    rv$t0 <- NULL
  }
  
  time_banner <- function() {
    l <- rv$log
    if (!nrow(l)) return(NULL)
    last <- l[nrow(l), ]
    div(class = "time-banner", icon("stopwatch"),
        HTML(paste0(" Found in <b>", fmt_time(last$Search_sec), "</b> instead of about <b>",
                    fmt_time(last$Manual_sec), "</b> of manual browsing - you saved <b>",
                    fmt_time(last$Saved_sec), "</b>.")))
  }
  
  short_cast <- function(x) {
    vapply(x, function(s) {
      if (is.na(s)) return(NA_character_)
      paste(head(strsplit(s, "; ", fixed = TRUE)[[1]], 4), collapse = ", ")
    }, "", USE.NAMES = FALSE)
  }
  
  # ------------------------------------------- RECOMMEND (taste-based)
  observeEvent(input$go, {
    b <- bundle(); df <- b$df
    liked <- as.integer(input$liked); fav <- input$fav_genres
    prof <- rep(0, ncol(b$X))
    if (length(liked)) prof <- colMeans(b$X[liked, , drop = FALSE])
    if (length(fav)) { idx <- match(fav, b$genres); prof[idx] <- prof[idx] + 1.6 }
    has_prof <- length(liked) > 0 || length(fav) > 0
    sim <- if (has_prof) pmax(0, as.numeric(b$Xn %*% (prof / sqrt(sum(prof^2))))) else rep(0, nrow(df))
    
    w <- switch(input$style, "Balanced" = c(.55, .30, .15),
                "Taste-first" = c(.75, .15, .10), "Quality-first" = c(.30, .50, .20))
    if (!has_prof) w <- c(0, w[2] / (w[2] + w[3]), w[3] / (w[2] + w[3]))
    score <- w[1] * sim + w[2] * df$ml_n + w[3] * df$pop_n
    
    ok <- df$year >= input$yr[1] & df$year <= input$yr[2] &
      df$rating >= input$min_rating & (is.na(df$runtime) | df$runtime <= input$max_rt)
    if (length(input$certs)) ok <- ok & df$certificate %in% input$certs
    if (length(liked)) ok[liked] <- FALSE
    cand <- which(ok)
    if (!length(cand)) {
      recs(NULL)
      showNotification("No movies match these filters - try relaxing them.", type = "warning")
      return()
    }
    top <- cand[order(score[cand], decreasing = TRUE)][seq_len(min(input$n_rec, length(cand)))]
    
    ug <- unique(c(fav, unlist(strsplit(df$genre[liked], ", ", fixed = TRUE))))
    liked_dirs <- df$director_main[liked]
    why <- vapply(top, function(i) {
      g <- intersect(ug, strsplit(df$genre[i], ", ", fixed = TRUE)[[1]])
      parts <- character()
      if (length(g)) parts <- c(parts, paste("Matches your taste for", paste(g, collapse = ", ")))
      if (!is.na(df$director_main[i]) && df$director_main[i] %in% liked_dirs)
        parts <- c(parts, "same director as a movie you liked")
      if (!length(parts)) parts <- "Top-rated pick predicted by the ML model"
      paste0(paste(parts, collapse = "; "), ".")
    }, "")
    
    r <- df[top, c("title", "year", "runtime", "certificate", "genre",
                   "director_main", "cast", "rating", "ml_pred")]
    r$cast <- short_cast(r$cast)
    r$match <- pmin(99, round(100 * score[top]))
    r$why <- why
    recs(r)
    log_search("Taste-based", df$title[top[1]])
  })
  
  output$rec_banner <- renderUI(time_banner())
  output$rec_cards <- renderUI({
    r <- recs()
    if (is.null(r)) div(class = "empty", icon("film"), br(),
                        "Choose a few movies or genres you like, then press ", tags$b("Recommend"), ".")
    else movie_cards(r)
  })
  
  # ----------------------------------------------- SIMILAR MOVIES
  observeEvent(input$go_sim, {
    req(input$sim_movie)
    b <- bundle(); df <- b$df
    i <- as.integer(input$sim_movie)
    s <- as.numeric(b$Xn %*% b$Xn[i, ])
    same_dir <- !is.na(df$director_main) & !is.na(df$director_main[i]) &
      df$director_main == df$director_main[i]
    target <- if (is.na(df$cast[i])) character(0) else strsplit(df$cast[i], "; ", fixed = TRUE)[[1]]
    shared <- if (length(target)) vapply(strsplit(df$cast, "; ", fixed = TRUE),
                                         function(v) sum(v %in% target), numeric(1)) else rep(0, nrow(df))
    s <- s + 0.15 * same_dir + 0.05 * pmin(shared, 3)
    s[i] <- -Inf
    top <- order(s, decreasing = TRUE)[seq_len(min(input$n_sim, nrow(df) - 1))]
    tg <- strsplit(df$genre[i], ", ", fixed = TRUE)[[1]]
    why <- vapply(top, function(j) {
      g <- intersect(tg, strsplit(df$genre[j], ", ", fixed = TRUE)[[1]])
      parts <- character()
      if (length(g)) parts <- c(parts, paste("Shares", paste(g, collapse = ", ")))
      if (same_dir[j]) parts <- c(parts, "same director")
      if (shared[j] > 0) parts <- c(parts, paste(shared[j], "shared cast member(s)"))
      if (!length(parts)) parts <- "Similar era, runtime and rating profile"
      paste0(paste(parts, collapse = "; "), ".")
    }, "")
    r <- df[top, c("title", "year", "runtime", "certificate", "genre",
                   "director_main", "cast", "rating", "ml_pred")]
    r$cast <- short_cast(r$cast)
    r$match <- pmin(99, round(100 * s[top]))
    r$why <- why
    sims(r)
    log_search("Similar movie", df$title[top[1]])
  })
  output$sim_banner <- renderUI(time_banner())
  output$sim_cards <- renderUI({
    r <- sims()
    if (is.null(r)) div(class = "empty", icon("clone"), br(),
                        "Pick a movie you enjoyed and press ", tags$b("Find similar"), ".")
    else movie_cards(r)
  })
  
  # -------------------------------------------------------- HOME
  output$vb_movies <- renderValueBox(valueBox(format(nrow(bundle()$df), big.mark = ","),
                                              "Movies in database", icon = icon("film"), color = "red"))
  output$vb_genres <- renderValueBox(valueBox(length(bundle()$genres), "Distinct genres",
                                              icon = icon("tags"), color = "black"))
  output$vb_avg <- renderValueBox(valueBox(round(mean(bundle()$df$rating), 2), "Average IMDb rating",
                                           icon = icon("star"), color = "maroon"))
  output$vb_saved <- renderValueBox({
    l <- rv$log
    valueBox(if (nrow(l)) fmt_time(mean(l$Saved_sec)) else "-", "Avg. time saved per search",
             icon = icon("stopwatch"), color = "navy")
  })
  output$home_decade <- renderPlotly({
    d <- bundle()$df %>% count(decade)
    plot_ly(d, x = ~decade, y = ~n, type = "bar", marker = list(color = RED)) %>%
      layout(xaxis = list(title = "Decade"), yaxis = list(title = "Movies")) %>% pl_style()
  })
  output$home_genre <- renderPlotly({
    d <- genres_long() %>% count(genre, sort = TRUE) %>% head(8)
    plot_ly(d, labels = ~genre, values = ~n, type = "pie", hole = 0.5,
            marker = list(colors = colorRampPalette(c(RED, "#141414"))(8))) %>% pl_style()
  })
  
  # ------------------------------------------------- DATA EXPLORER
  output$p_missing <- renderPlotly({
    df <- bundle()$df
    cols <- c("runtime", "certificate", "director_main", "cast", "metascore", "votes", "gross")
    m <- sapply(df[cols], function(x) round(mean(is.na(x)) * 100, 1))
    plot_ly(x = names(m), y = as.numeric(m), type = "bar", marker = list(color = RED),
            text = paste0(m, "%"), textposition = "outside") %>%
      layout(yaxis = list(title = "% missing")) %>% pl_style()
  })
  output$tbl_summary <- renderTable({
    df <- bundle()$df
    cols <- c("year", "runtime", "rating", "metascore", "votes", "gross")
    do.call(rbind, lapply(cols, function(cn) {
      x <- df[[cn]]
      data.frame(Variable = cn, Min = min(x, na.rm = TRUE), Median = median(x, na.rm = TRUE),
                 Mean = round(mean(x, na.rm = TRUE), 2), Max = max(x, na.rm = TRUE))
    }))
  }, digits = 2)
  display_df <- reactive({
    df <- bundle()$df
    data.frame(Title = df$title, Year = df$year, Runtime = df$runtime,
               Certificate = df$certificate, Genre = df$genre, Director = df$director_main,
               Cast = df$cast, Rating = df$rating, Metascore = df$metascore,
               Votes = df$votes, Gross_M = df$gross, stringsAsFactors = FALSE)
  })
  output$tbl_data <- renderDT(datatable(display_df(), filter = "top", rownames = FALSE,
                                        options = list(pageLength = 12, scrollX = TRUE)))
  output$dl_data <- downloadHandler(
    filename = function() paste0("cinematch_filtered_", Sys.Date(), ".csv"),
    content = function(file) {
      rows <- input$tbl_data_rows_all
      d <- display_df()
      write.csv(if (length(rows)) d[rows, ] else d, file, row.names = FALSE)
    })
  
  # ------------------------------------------------ RATINGS & GENRES
  output$p_hist <- renderPlotly({
    plot_ly(bundle()$df, x = ~rating, type = "histogram", nbinsx = 40,
            marker = list(color = RED, line = list(color = "white", width = 1))) %>%
      layout(xaxis = list(title = "IMDb rating"), yaxis = list(title = "Movies")) %>% pl_style()
  })
  output$p_genre_count <- renderPlotly({
    d <- genres_long() %>% count(genre, sort = TRUE) %>% head(15)
    plot_ly(d, x = ~n, y = ~genre, type = "bar", orientation = "h", marker = list(color = RED)) %>%
      layout(yaxis = list(categoryorder = "total ascending", title = ""),
             xaxis = list(title = "Movies")) %>% pl_style()
  })
  output$p_genre_box <- renderPlotly({
    gl <- genres_long()
    top <- gl %>% count(genre, sort = TRUE) %>% head(12) %>% pull(genre)
    plot_ly(gl %>% filter(genre %in% top), x = ~genre, y = ~rating, type = "box",
            marker = list(color = RED), line = list(color = DARK)) %>%
      layout(xaxis = list(title = ""), yaxis = list(title = "Rating")) %>% pl_style()
  })
  output$p_genre_avg <- renderPlotly({
    d <- genres_long() %>% group_by(genre) %>%
      summarise(avg = mean(rating), n = n(), .groups = "drop") %>% filter(n >= 10) %>%
      arrange(desc(avg)) %>% head(15)
    plot_ly(d, x = ~avg, y = ~genre, type = "bar", orientation = "h",
            marker = list(color = RED), text = ~round(avg, 2), textposition = "outside") %>%
      layout(yaxis = list(categoryorder = "total ascending", title = ""),
             xaxis = list(title = "Average rating", range = c(min(d$avg) - 0.5, max(d$avg) + 0.3))) %>%
      pl_style()
  })
  output$p_cert <- renderPlotly({
    d <- bundle()$df %>% mutate(certificate = ifelse(is.na(certificate), "Unrated", certificate)) %>%
      count(certificate, sort = TRUE) %>% head(15)
    plot_ly(d, x = ~certificate, y = ~n, type = "bar", marker = list(color = DARK)) %>%
      layout(xaxis = list(categoryorder = "total descending", title = ""),
             yaxis = list(title = "Movies")) %>% pl_style()
  })
  
  # ------------------------------------------------------- TRENDS
  trend_df <- reactive({
    bundle()$df %>% filter(year >= input$trend_years[1], year <= input$trend_years[2])
  })
  output$p_peryear <- renderPlotly({
    d <- trend_df() %>% count(year)
    plot_ly(d, x = ~year, y = ~n, type = "scatter", mode = "lines",
            line = list(color = RED, width = 2), fill = "tozeroy",
            fillcolor = "rgba(229,9,20,0.15)") %>%
      layout(xaxis = list(title = "Year"), yaxis = list(title = "Movies")) %>% pl_style()
  })
  output$p_decade_rating <- renderPlotly({
    d <- trend_df() %>% group_by(decade) %>%
      summarise(Rating = mean(rating), Metascore = mean(metascore, na.rm = TRUE) / 10, .groups = "drop")
    plot_ly(d, x = ~decade) %>%
      add_lines(y = ~Rating, name = "IMDb rating", line = list(color = RED)) %>%
      add_lines(y = ~Metascore, name = "Metascore / 10", line = list(color = DARK, dash = "dot")) %>%
      layout(xaxis = list(title = "Decade"), yaxis = list(title = "Score"),
             legend = list(orientation = "h")) %>% pl_style()
  })
  output$p_runtime <- renderPlotly({
    d <- trend_df() %>% group_by(decade) %>% summarise(rt = mean(runtime, na.rm = TRUE), .groups = "drop")
    plot_ly(d, x = ~decade, y = ~rt, type = "bar", marker = list(color = RED)) %>%
      layout(xaxis = list(title = "Decade"), yaxis = list(title = "Avg runtime (min)")) %>% pl_style()
  })
  output$p_votes_scatter <- renderPlotly({
    d <- trend_df() %>% filter(!is.na(votes), votes > 0)
    if (nrow(d) > 5000) d <- d[sample.int(nrow(d), 5000), ]
    plot_ly(d, x = ~votes, y = ~rating, type = "scatter", mode = "markers", text = ~title,
            marker = list(color = RED, opacity = 0.4, size = 6)) %>%
      layout(xaxis = list(type = "log", title = "Votes (log)"), yaxis = list(title = "Rating")) %>%
      pl_style()
  })
  output$p_meta_scatter <- renderPlotly({
    d <- trend_df() %>% filter(!is.na(metascore))
    validate(need(nrow(d) > 5, "Not enough metascore data in this range."))
    if (nrow(d) > 5000) d <- d[sample.int(nrow(d), 5000), ]
    fit <- lm(rating ~ metascore, data = d)
    xs <- seq(min(d$metascore), max(d$metascore), length.out = 50)
    plot_ly(d, x = ~metascore, y = ~rating, type = "scatter", mode = "markers", text = ~title,
            marker = list(color = RED, opacity = 0.4, size = 6), name = "Movies") %>%
      add_lines(x = xs, y = predict(fit, data.frame(metascore = xs)), name = "Trend",
                line = list(color = DARK), inherit = FALSE) %>%
      layout(xaxis = list(title = "Metascore"), yaxis = list(title = "IMDb rating")) %>% pl_style()
  })
  
  # ------------------------------------------------------- PEOPLE
  hbar <- function(d, x, y, xlab) {
    plot_ly(d, x = d[[x]], y = d[[y]], type = "bar", orientation = "h",
            marker = list(color = RED)) %>%
      layout(yaxis = list(categoryorder = "total ascending", title = ""),
             xaxis = list(title = xlab), margin = list(l = 140)) %>% pl_style()
  }
  dir_stats <- reactive({
    bundle()$df %>% filter(!is.na(director_main)) %>% group_by(director_main) %>%
      summarise(n = n(), avg = round(mean(rating), 2), .groups = "drop")
  })
  act_stats <- reactive({
    cast_long() %>% group_by(cast) %>%
      summarise(n = n(), avg = round(mean(rating), 2), .groups = "drop")
  })
  output$p_dir_avg <- renderPlotly({
    d <- dir_stats() %>% filter(n >= input$min_movies) %>% arrange(desc(avg)) %>% head(15)
    validate(need(nrow(d) > 0, "No directors meet this threshold."))
    hbar(d, "avg", "director_main", "Average rating")
  })
  output$p_dir_count <- renderPlotly({
    hbar(dir_stats() %>% arrange(desc(n)) %>% head(15), "n", "director_main", "Movies")
  })
  output$p_act_avg <- renderPlotly({
    d <- act_stats() %>% filter(n >= input$min_movies) %>% arrange(desc(avg)) %>% head(15)
    validate(need(nrow(d) > 0, "No actors meet this threshold."))
    hbar(d, "avg", "cast", "Average rating")
  })
  output$p_act_count <- renderPlotly({
    hbar(act_stats() %>% arrange(desc(n)) %>% head(15), "n", "cast", "Movies")
  })
  
  # --------------------------------------------------- CORRELATION
  output$p_corr <- renderPlotly({
    df <- bundle()$df
    cm <- cor(df[, c("year", "runtime", "rating", "metascore", "votes", "gross")],
              use = "pairwise.complete.obs")
    cm <- round(cm, 2)
    plot_ly(x = colnames(cm), y = rownames(cm), z = cm, type = "heatmap",
            colorscale = list(c(0, "#2c7bb6"), c(0.5, "#ffffff"), c(1, RED)),
            zmin = -1, zmax = 1) %>%
      add_annotations(x = rep(colnames(cm), each = nrow(cm)), y = rep(rownames(cm), ncol(cm)),
                      text = as.character(as.vector(cm)), showarrow = FALSE,
                      font = list(size = 11)) %>% pl_style()
  })
  output$p_gross_top <- renderPlotly({
    d <- bundle()$df %>% filter(!is.na(gross)) %>% arrange(desc(gross)) %>% head(15)
    validate(need(nrow(d) > 0, "No gross data available."))
    hbar(d, "gross", "title", "Gross (USD millions)")
  })
  output$p_runtime_hist <- renderPlotly({
    plot_ly(bundle()$df %>% filter(!is.na(runtime)), x = ~runtime, type = "histogram", nbinsx = 50,
            marker = list(color = DARK)) %>%
      layout(xaxis = list(title = "Runtime (min)"), yaxis = list(title = "Movies")) %>% pl_style()
  })
  output$p_votes_top <- renderPlotly({
    d <- bundle()$df %>% filter(!is.na(votes)) %>% arrange(desc(votes)) %>% head(15)
    hbar(d, "votes", "title", "Votes")
  })
  
  # ----------------------------------------------------- ML PERFORMANCE
  mdl <- reactive(bundle()$model)
  best <- reactive({ m <- mdl()$metrics; m[which.min(m$RMSE), ] })
  output$vb_best <- renderValueBox(valueBox(best()$Model, "Best model (lowest RMSE)",
                                            icon = icon("trophy"), color = "red"))
  output$vb_rmse <- renderValueBox(valueBox(best()$RMSE, "RMSE (rating points)",
                                            icon = icon("bullseye"), color = "black"))
  output$vb_r2 <- renderValueBox(valueBox(best()$R2, "R\u00B2 on test data",
                                          icon = icon("chart-line"), color = "maroon"))
  output$vb_split <- renderValueBox(valueBox(paste0(format(mdl()$train_n, big.mark = ","), " / ",
                                                    format(mdl()$test_n, big.mark = ",")),
                                             "Train / test movies", icon = icon("database"), color = "navy"))
  output$tbl_metrics <- renderTable(mdl()$metrics, digits = 3)
  output$p_rmse <- renderPlotly({
    m <- mdl()$metrics
    plot_ly(m, x = ~Model, y = ~RMSE, type = "bar", marker = list(color = c(RED, "#777", "#bbb")),
            text = ~RMSE, textposition = "outside") %>%
      layout(yaxis = list(title = "RMSE (lower is better)")) %>% pl_style()
  })
  output$p_avp <- renderPlotly({
    m <- mdl()
    d <- data.frame(actual = m$test_actual, pred = m$test_pred)
    if (nrow(d) > 3000) d <- d[sample.int(nrow(d), 3000), ]
    plot_ly(d, x = ~actual, y = ~pred, type = "scatter", mode = "markers",
            marker = list(color = RED, opacity = 0.35, size = 6), name = "Movies") %>%
      add_lines(x = c(1, 10), y = c(1, 10), line = list(color = DARK, dash = "dash"),
                name = "Perfect", inherit = FALSE) %>%
      layout(xaxis = list(title = "Actual rating"), yaxis = list(title = "Predicted rating")) %>% pl_style()
  })
  output$p_imp <- renderPlotly({
    d <- head(mdl()$imp, 15)
    hbar(d, "Importance", "Feature", "Importance (%IncMSE)")
  })
  output$p_resid <- renderPlotly({
    m <- mdl()
    plot_ly(x = m$test_actual - m$test_pred, type = "histogram", nbinsx = 40,
            marker = list(color = DARK)) %>%
      layout(xaxis = list(title = "Actual - predicted"), yaxis = list(title = "Movies")) %>% pl_style()
  })
  
  # --------------------------------------------------- RATING PREDICTOR
  pred_vals <- eventReactive(input$go_pred, {
    m <- mdl()
    validate(need(length(input$p_genres) > 0, "Select at least one genre."))
    d <- data.frame(year = input$p_year, runtime = input$p_runtime, certificate = input$p_cert,
                    genre = paste(input$p_genres, collapse = ", "), votes = input$p_votes,
                    metascore = if (isTRUE(input$p_meta > 0)) input$p_meta else NA_real_,
                    gross = if (isTRUE(input$p_gross > 0)) input$p_gross else NA_real_,
                    stringsAsFactors = FALSE)
    nd <- ml_frame(d, m$genres, m$cert_levels, m$med)
    cl <- function(x) round(min(10, max(1, as.numeric(x))), 2)
    list(rf = cl(predict(m$rf, nd)), lm = cl(suppressWarnings(predict(m$lm, nd))),
         tree = cl(predict(m$tree, nd)))
  })
  output$vb_p_rf <- renderValueBox(valueBox(pred_vals()$rf, "Random Forest", icon = icon("tree"), color = "red"))
  output$vb_p_lm <- renderValueBox(valueBox(pred_vals()$lm, "Linear Regression", icon = icon("chart-line"), color = "black"))
  output$vb_p_tree <- renderValueBox(valueBox(pred_vals()$tree, "Decision Tree", icon = icon("sitemap"), color = "maroon"))
  output$pred_verdict <- renderUI({
    p <- pred_vals()$rf
    verdict <- if (p >= 8) "A potential must-watch (8+)." else if (p >= 7) "A good movie (7 - 8)." else
      if (p >= 6) "Decent, but not outstanding (6 - 7)." else "Likely to be a weak or niche title (below 6)."
    box(width = 12, status = "danger", solidHeader = TRUE, title = "Verdict",
        h3(paste0("\u2605 ", p, " / 10")), p(verdict),
        div(class = "small-note", "Predictions come from models trained on your dataset; ",
            "the Random Forest is used inside the recommender."))
  })
  
  # ---------------------------------------------------------- TIME SAVED
  stats <- reactive({
    l <- rv$log
    if (!nrow(l)) return(NULL)
    list(n = nrow(l), avg = mean(l$Saved_sec), total = sum(l$Saved_sec),
         pct = 100 * sum(l$Saved_sec) / sum(l$Manual_sec))
  })
  output$vb_n <- renderValueBox(valueBox(nrow(rv$log), "Searches done", icon = icon("search"), color = "red"))
  output$vb_avgsave <- renderValueBox({
    s <- stats(); valueBox(if (is.null(s)) "-" else fmt_time(s$avg), "Average time saved / search",
                           icon = icon("stopwatch"), color = "black")
  })
  output$vb_totalsave <- renderValueBox({
    s <- stats(); valueBox(if (is.null(s)) "-" else fmt_time(s$total), "Total time saved",
                           icon = icon("hourglass-half"), color = "maroon")
  })
  output$vb_pct <- renderValueBox({
    s <- stats(); valueBox(if (is.null(s)) "-" else paste0(round(s$pct, 1), "%"), "Faster than manual search",
                           icon = icon("bolt"), color = "navy")
  })
  output$p_compare <- renderPlotly({
    l <- rv$log
    validate(need(nrow(l) > 0, "Run a recommendation to see results here."))
    plot_ly(l, x = ~factor(No)) %>%
      add_bars(y = ~Manual_sec / 60, name = "Manual browsing", marker = list(color = "#999")) %>%
      add_bars(y = ~Search_sec / 60, name = "CineMatch", marker = list(color = RED)) %>%
      layout(barmode = "group", xaxis = list(title = "Search #"), yaxis = list(title = "Minutes"),
             legend = list(orientation = "h")) %>% pl_style()
  })
  output$p_cum <- renderPlotly({
    l <- rv$log
    validate(need(nrow(l) > 0, "Run a recommendation to see results here."))
    plot_ly(x = l$No, y = cumsum(l$Saved_sec) / 60, type = "scatter", mode = "lines+markers",
            line = list(color = RED), marker = list(color = RED)) %>%
      layout(xaxis = list(title = "Search #", dtick = 1), yaxis = list(title = "Minutes saved")) %>% pl_style()
  })
  output$projection <- renderUI({
    s <- stats()
    if (is.null(s)) return(p("Make at least one recommendation to see a projection."))
    mon <- s$avg * input$per_month
    tagList(h4(paste0("About ", fmt_time(mon), " saved per month")),
            p(paste0("That is roughly ", round(mon * 12 / 3600, 1), " hours per year at ",
                     input$per_month, " movies a month.")))
  })
  output$tbl_log <- renderDT({
    l <- rv$log
    l$Search <- paste0(round(l$Search_sec), " s")
    l$Manual <- paste0(round(l$Manual_sec / 60, 1), " min")
    l$Saved <- vapply(l$Saved_sec, fmt_time, "")
    datatable(l[, c("No", "Time", "Mode", "Pick", "Search", "Manual", "Saved")],
              rownames = FALSE, options = list(pageLength = 8, dom = "tp"))
  })
  observeEvent(input$reset_log, { rv$log <- empty_log(); rv$t0 <- NULL })
}

shinyApp(ui, server)